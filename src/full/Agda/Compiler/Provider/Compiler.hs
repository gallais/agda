{-# LANGUAGE CPP             #-}

module Agda.Compiler.Provider.Compiler
       (
         provide
       ) where

import Data.IORef
import Data.Map ( Map )
import qualified Data.Map as Map
import Data.Maybe ( catMaybes, fromMaybe )
import Data.Tuple ( swap )

import Control.Monad.IO.Class

import System.IO.Unsafe

import Agda.Compiler.Backend
import Agda.Compiler.MAlonzo.Compiler
  ( GHCOptions, GHCModuleEnv, ghcCompileDef, ghcBackend' )
import Agda.Compiler.MAlonzo.HaskellTypes ( getHsType', haskellType' )
import Agda.Compiler.MAlonzo.Misc ( unqhname, dname )

import Agda.Syntax.Common
import Agda.Syntax.Internal

import Agda.TypeChecking.Monad.Base
import Agda.TypeChecking.Monad.Builtin
import Agda.TypeChecking.Pretty
import Agda.TypeChecking.Primitive
import Agda.TypeChecking.Warnings

import Agda.Utils.Functor
import qualified Agda.Utils.Haskell.Syntax as HS
import Agda.Utils.Lens
import Agda.Utils.List ( wordsBy )

#include "undefined.h"
import Agda.Utils.Impossible

-- The entrypoint

provide :: Interface -> TCM (FilePath, Map QName String)
provide i = do
  liftIO $ writeIORef phoneBook Map.empty
  bTypes <- builtinTypes
  locallyState stBackends (providerBackend :) $ do
    visitModule $ ModuleInfo
                { miInterface  = i
                , miWarnings   = False
                }
    callBackend (backendName providerBackend') NotMain i
  pb <- liftIO $ readIORef phoneBook
  return ("", pb) -- TODO: not sure how to grab the file's name reliably

builtinTypes :: TCM [(HS.Type, String)]
builtinTypes = do
  qn <- catMaybes <$> mapM (fmap sequenceA . traverse getBuiltinName)
                   [ ("Nat"   , builtinNat)
                   , ("Word64", builtinWord64)
                   , ("Float" , builtinFloat)
                   , ("String", builtinString)
                   , ("Char"  , builtinChar)
                   ]
  htys <- mapM (traverse getHsType') qn
  return $ swap <$> htys

-- The backend callbacks --------------------------------------------------

providerBackend :: Backend
providerBackend = Backend providerBackend'

providerBackend' :: Backend' GHCOptions GHCOptions GHCModuleEnv IsMain [HS.Decl]
providerBackend' = ghcBackend' { backendName    = "Provider"
                               , backendVersion = Just "AIM Buda"
                               , compileDef     = providerCompileDef
                               }

providerCompileDef :: GHCOptions -> GHCModuleEnv -> Definition -> TCM [HS.Decl]
providerCompileDef ghco ghcme d = do
  cs  <- ghcCompileDef ghco ghcme d
  cs' <- case theDef d of
    f@Function{} | funProvide f -> providerWrapper (defType d) (defName d)
    _ -> pure []
  return $ cs' ++ cs

rtePrefix :: String -> HS.QName
rtePrefix nm = HS.ModuleName "MAlonzo.RTE" `HS.Qual` HS.Ident nm

data ToOrFrom = To | From { underIO :: Bool }
  deriving Eq

-- | In @isLiteral b ty@ defines a functions @toTy@ converting from @Literal@ to @ty@
-- or @fromTy@ converting from @ty@ to @Literal@ depending on the value of @b@ of type
-- @ToOrFrom@.
-- In the @From@ case, @ty@ is allowed to be @IO ty'@ where @ty'@ is also a literal.

isLiteral :: [(HS.Type, String)] -> ToOrFrom -> HS.Type -> Maybe HS.Exp
isLiteral bTypes tof ty = case ty of
  HS.TyApp (HS.TyApp (HS.TyCon ioName) _) a | From{} <- tof ->
    HS.App (HS.Var (HS.UnQual (HS.Ident "fmap")))
    <$> isLiteral bTypes (From True) a
  -- TODO: case + document
  a -> for (toOrFrom a) $ \ conv -> case tof of
    To           -> conv
    From underIO ->
      if underIO then conv
      else HS.InfixApp (HS.Var (HS.UnQual (HS.Ident "return")))
                       (HS.QVarOp (HS.UnQual (HS.Symbol "."))) conv

  where

    toOrFrom :: HS.Type -> Maybe HS.Exp
    toOrFrom nm = for (lookup nm bTypes) $ \ lit ->
      let prefix = case tof of { To -> "to";  From{} -> "" }
      in HS.Var . rtePrefix $ prefix ++ "Lit" ++ lit

phoneBook :: IORef (Map QName String)
phoneBook = unsafePerformIO (newIORef Map.empty)

nameSupply :: IORef Integer
nameSupply = unsafePerformIO (newIORef 0)

gimmeNames :: IO (HS.Name, HS.Name)
gimmeNames = do
  n <- readIORef nameSupply
  writeIORef nameSupply (1 + n)
  return ( HS.Ident ("lit"   ++ show n)
         , HS.Ident ("lits" ++ show n)
         )

-- compileWrapper (a -> bs) f =
-- (fromA, toA) <- compileLiteral a
-- return $ \ (x : xs) -> compileWrapper bs (f (toA x)) xs

-- compileWrapper a f =
-- (fromA, toA) <- compileLiteral a
-- return $ \ [] -> fromA f

compileWrapper :: [(HS.Type, String)] -> HS.Type -> HS.Exp -> TCM HS.Exp
compileWrapper bTypes t f = case t of
  HS.TyFun a b -> do
    let toA = fromMaybe __IMPOSSIBLE__ $ isLiteral bTypes To a
    (x, xs) <- liftIO gimmeNames
    f' <- compileWrapper bTypes b $ HS.App f
      $ HS.App toA (HS.Var (HS.UnQual x))
    return $ HS.Lambda [HS.PApp cons (HS.PVar <$> [x, xs])]
           $ HS.App f' (HS.Var (HS.UnQual xs))
  a -> do
    let fromA = fromMaybe __IMPOSSIBLE__ $ isLiteral bTypes (From False) a
    return $ HS.Lambda [HS.PApp nil []]
           $ HS.App fromA f

  where

    nil  = HS.UnQual (HS.Ident "[]")
    cons = HS.UnQual (HS.Symbol ":")

providerWrapper :: Type -> QName -> TCM [HS.Decl]
providerWrapper t qn = do
  hty  <- haskellType' t
  bTypes <- builtinTypes
  wrap <- compileWrapper bTypes hty (HS.Var (HS.UnQual (dname qn)))
  let pn@(HS.Ident rawpn) = unqhname "provide" qn
  liftIO $ modifyIORef' phoneBook (Map.insert qn rawpn)
  return [ HS.TypeSig [pn] (HS.TyFun literals (HS.TyApp (HS.TyApp (HS.TyCon ioName) (HS.TyCon (HS.UnQual (HS.Ident "AgdaAny")))) literal))
         , HS.FunBind [HS.Match pn [] (HS.UnGuardedRhs wrap) Nothing]
         ]
  -- TODO: insert qn pn
  -- which object file are these going to end up in?
  where
    literals = HS.TyApp (HS.TyCon (HS.UnQual (HS.Ident "[]"))) literal
    literal  = HS.TyCon (rtePrefix "Literal")

ioName :: HS.QName
ioName = HS.UnQual $ HS.Ident "MAlonzo.Code.Agda.Builtin.IO.T8"
