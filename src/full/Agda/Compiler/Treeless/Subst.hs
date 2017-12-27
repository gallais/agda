{-# LANGUAGE CPP #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}

module Agda.Compiler.Treeless.Subst where

import qualified Data.Map as Map
import Data.Map (Map)
import Data.Maybe
import Data.Monoid ( Monoid, mempty, mappend )
import Data.Semigroup ( Semigroup, (<>), All(..), Any(..) )

import Agda.Syntax.Treeless
import Agda.Syntax.Internal (Substitution'(..))
import Agda.TypeChecking.Substitute

import Agda.Utils.Impossible
#include "undefined.h"

instance DeBruijn TTerm where
  deBruijnVar = TVar
  deBruijnView (TVar i) = Just i
  deBruijnView _ = Nothing

instance Subst TTerm TTerm where
  applySubst IdS t = t
  applySubst rho t = case t of
      TDef{}    -> t
      TLit{}    -> t
      TCon{}    -> t
      TPrim{}   -> t
      TUnit{}   -> t
      TSort{}   -> t
      TErased{} -> t
      TError{}  -> t
      TVar i         -> lookupS rho i
      TApp f ts      -> tApp (applySubst rho f) (applySubst rho ts)
      TLam nh b      -> TLam nh (applySubst (liftS 1 rho) b)
      TLet nh e b    -> TLet nh (applySubst rho e) (applySubst (liftS 1 rho) b)
      TCase i t d bs ->
        case applySubst rho (TVar i) of
          TVar j  -> TCase j t (applySubst rho d) (applySubst rho bs)
          e       -> TLet noNHint e $ TCase 0 t (applySubst rho' d) (applySubst rho' bs)
            where rho' = wkS 1 rho
      TCoerce e -> TCoerce (applySubst rho e)
    where
      tApp (TPrim PSeq) [TErased, b] = b
      tApp f ts = TApp f ts

instance Subst TTerm TAlt where
  applySubst rho (TACon c i nhs b) = TACon c i nhs (applySubst (liftS i rho) b)
  applySubst rho (TALit l b)       = TALit l (applySubst rho b)
  applySubst rho (TAGuard g b)     = TAGuard (applySubst rho g) (applySubst rho b)

newtype UnderLambda = UnderLambda Any
  deriving (Eq, Ord, Show, Semigroup, Monoid)

newtype SeqArg = SeqArg All
  deriving (Eq, Ord, Show, Semigroup, Monoid)

data Occurs = Occurs Int UnderLambda SeqArg
  deriving (Eq, Ord, Show)

once :: Occurs
once = Occurs 1 mempty (SeqArg $ All False)

inSeq :: Occurs -> Occurs
inSeq (Occurs n l _) = Occurs n l mempty

underLambda :: Occurs -> Occurs
underLambda o = o <> Occurs 0 (UnderLambda $ Any True) mempty

instance Semigroup Occurs where
  Occurs a k s <> Occurs b l t = Occurs (a + b) (k <> l) (s <> t)

instance Monoid Occurs where
  mempty  = Occurs 0 mempty mempty
  mappend = (<>)

class HasFree a where
  freeVars :: a -> Map Int Occurs

freeIn :: HasFree a => Int -> a -> Bool
freeIn i x = Map.member i (freeVars x)

occursIn :: HasFree a => Int -> a -> Occurs
occursIn i x = fromMaybe mempty $ Map.lookup i (freeVars x)

instance HasFree Int where
  freeVars x = Map.singleton x once

instance HasFree a => HasFree [a] where
  freeVars xs = Map.unionsWith mappend $ map freeVars xs

instance (HasFree a, HasFree b) => HasFree (a, b) where
  freeVars (x, y) = Map.unionWith mappend (freeVars x) (freeVars y)

data Binder a = Binder Int a

instance HasFree a => HasFree (Binder a) where
  freeVars (Binder 0 x) = freeVars x
  freeVars (Binder k x) = Map.filterWithKey (\ k _ -> k >= 0) $ Map.mapKeysMonotonic (subtract k) $ freeVars x

newtype InSeq a = InSeq a

instance HasFree a => HasFree (InSeq a) where
  freeVars (InSeq x) = inSeq <$> freeVars x

instance HasFree TTerm where
  freeVars t = case t of
    TDef{}    -> Map.empty
    TLit{}    -> Map.empty
    TCon{}    -> Map.empty
    TPrim{}   -> Map.empty
    TUnit{}   -> Map.empty
    TSort{}   -> Map.empty
    TErased{} -> Map.empty
    TError{}  -> Map.empty
    TVar i         -> freeVars i
    TApp (TPrim PSeq) [TVar x, b] -> freeVars (InSeq x, b)
    TApp f ts      -> freeVars (f, ts)
    TLam _ b       -> underLambda <$> freeVars (Binder 1 b)
    TLet _ e b     -> freeVars (e, Binder 1 b)
    TCase i _ d bs -> freeVars (i, (d, bs))
    TCoerce t      -> freeVars t

instance HasFree TAlt where
  freeVars a = case a of
    TACon _ i _ b -> freeVars (Binder i b)
    TALit _ b     -> freeVars b
    TAGuard g b   -> freeVars (g, b)

-- | Strenghtening.
tryStrengthen :: (HasFree a, Subst t a) => Int -> a -> Maybe a
tryStrengthen n t =
  case Map.minViewWithKey (freeVars t) of
    Just ((i, _), _) | i < n -> Nothing
    _ -> Just $ applySubst (strengthenS __IMPOSSIBLE__ n) t
