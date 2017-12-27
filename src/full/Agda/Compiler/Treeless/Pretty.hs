
{-# OPTIONS_GHC -fno-warn-orphans #-}

module Agda.Compiler.Treeless.Pretty () where

import Control.Arrow ((&&&), (***), first, second)
import Control.Monad.Reader
import Data.Maybe
import qualified Data.Map as Map

import Agda.Syntax.Treeless
import Agda.Compiler.Treeless.Subst
import Agda.Utils.Pretty

data PEnv = PEnv { pPrec :: Int
                 , pFresh :: [String]
                 , pBound :: [String] }

type P = Reader PEnv

withName :: NHint -> (String -> P a) -> P a
withName nh k = withNames [nh] $ \[x] -> k x

withNames :: [NHint] -> ([String] -> P a) -> P a
withNames nhs k = do
  let n = length nhs
  (xs, ys) <- asks $ splitAt n . pFresh
  local (\ e -> e { pFresh = ys }) (k xs)

-- | Don't generate fresh names for unused variables.
withNames' :: HasFree a => [NHint] -> a -> ([String] -> P b) -> P b
withNames' nhs tm k = withNames n' $ k . insBlanks
  where
    n = length nhs
    fv = freeVars tm
    n'  = (nhs !!) <$> filter (< n) (Map.keys fv)
    insBlanks = go n
      where
        go 0 _ = []
        go i xs0@(~(x : xs))
          | Map.member (i - 1) fv = x   : go (i - 1) xs
          | otherwise             = "_" : go (i - 1) xs0

bindName :: String -> P a -> P a
bindName x = local $ \ e -> e { pBound = x : pBound e }

bindNames :: [String] -> P a -> P a
bindNames xs p = foldr bindName p xs

paren :: Int -> P Doc -> P Doc
paren p doc = do
  n <- asks pPrec
  (if p < n then parens else id) <$> doc

prec :: Int -> P a -> P a
prec p = local $ \ e -> e { pPrec = p }

name :: Int -> P String
name x = asks $ (!! x) . (++ map (("^" ++) . show) [1..]) . pBound

runP :: P a -> a
runP p = runReader p PEnv{ pPrec = 0, pFresh = names, pBound = [] }
  where
    names = [ x ++ i | i <- "" : map show [1..], x <- map (:[]) ['a'..'z'] ]

instance Pretty TTerm where
  prettyPrec p t = runP $ prec p (pTerm t)

opName :: TPrim -> String
opName PAdd = "+"
opName PSub = "-"
opName PMul = "*"
opName PQuot = "quot"
opName PRem = "rem"
opName PGeq = ">="
opName PLt  = "<"
opName PEqI = "==I"
opName PAdd64 = "+64"
opName PSub64 = "-64"
opName PMul64 = "*64"
opName PQuot64 = "quot64"
opName PRem64 = "rem64"
opName PLt64  = "<64"
opName PEq64 = "==64"
opName PEqF = "==F"
opName PEqS = "==S"
opName PEqC = "==C"
opName PEqQ = "==Q"
opName PIf  = "if_then_else_"
opName PSeq = "seq"
opName PITo64 = "toWord64"
opName P64ToI = "fromWord64"


isInfix :: TPrim -> Maybe (Int, Int, Int)
isInfix op =
  case op of
    PMul -> l 7
    PAdd -> l 6
    PSub -> l 6
    PGeq -> non 4
    PLt  -> non 4
    PMul64 -> l 7
    PAdd64 -> l 6
    PSub64 -> l 6
    PLt64  -> non 4
    p | isPrimEq p -> non 4
    _    -> Nothing
  where
    l n   = Just (n, n, n + 1)
    r n   = Just (n, n + 1, n)
    non n = Just (n, n + 1, n + 1)

pTerm' :: Int -> TTerm -> P Doc
pTerm' p = prec p . pTerm

pTerm :: TTerm -> P Doc
pTerm t = case t of
  TVar x -> text <$> name x
  TApp (TPrim op) [a, b] | Just (c, l, r) <- isInfix op ->
    paren c $ sep <$> sequence [ pTerm' l a
                               , pure $ text $ opName op
                               , pTerm' r b ]
  TApp (TPrim PIf) [a, b, c] ->
    paren 0 $ (\ a b c -> sep [ text "if" <+> a
                              , nest 2 $ text "then" <+> b
                              , nest 2 $ text "else" <+> c ])
              <$> pTerm' 0 a
              <*> pTerm' 0 b
              <*> pTerm c
  TDef f -> pure $ pretty f
  TCon c -> pure $ pretty c
  TLit l -> pure $ pretty l
  TPrim op | isJust (isInfix op) -> pure $ text ("_" ++ opName op ++ "_")
           | otherwise -> pure $ text (opName op)
  TApp f es ->
    paren 9 $ (\a bs -> sep [a, nest 2 $ fsep bs])
              <$> pTerm' 9 f
              <*> mapM (pTerm' 10) es
  TLam _ _ -> paren 0 $ withNames' nhs b $ \ xs -> bindNames xs $
    (\b -> sep [ text ("λ " ++ unwords xs ++ " →")
               , nest 2 b ]) <$> pTerm' 0 b
    where
      (nhs, b) = tLamView t
  TLet{} -> paren 0 $ withNames nhs $ \ xs ->
    (\ (binds, b) -> sep [ text "let" <+> vcat [ sep [ text x <+> text "="
                                                     , nest 2 e ] | (x, e) <- binds ]
                              <+> text "in", b ])
      <$> pLets (zip xs es) b
    where
      (nhs, es) = unzip nhes
      (nhes, b) = tLetView t

      pLets [] b = ([],) <$> pTerm' 0 b
      pLets ((x, e) : bs) b = do
        e <- pTerm' 0 e
        first ((x, e) :) <$> bindName x (pLets bs b)

  TCase x _ def alts -> paren 0 $
    (\ sc alts defd ->
      sep [ text "case" <+> sc <+> text "of"
          , nest 2 $ vcat (alts ++ [ text "_ →" <+> defd | null alts || def /= TError TUnreachable ]) ]
    ) <$> pTerm' 0 (TVar x)
      <*> mapM pAlt alts
      <*> pTerm' 0 def
    where
      pAlt (TALit l b) = pAlt' <$> pTerm' 0 (TLit l) <*> pTerm' 0 b
      pAlt (TAGuard g b) =
        pAlt' <$> ((text "_" <+> text "|" <+>) <$> pTerm' 0 g)
              <*> (pTerm' 0 b)
      pAlt (TACon c a nhs b) =
        withNames' nhs b $ \ xs -> bindNames xs $
        pAlt' <$> pTerm' 0 (TApp (TCon c) [TVar i | i <- reverse [0..a - 1]])
              <*> pTerm' 0 b
      pAlt' p b = sep [p <+> text "→", nest 2 b]

  TUnit -> pure $ text "()"
  TSort -> pure $ text "Set"
  TErased -> pure $ text "_"
  TError err -> paren 9 $ pure $ text "error" <+> text (show (show err))
  TCoerce t -> paren 9 $ (text "coe" <+>) <$> pTerm' 10 t
