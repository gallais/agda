module Agda.Compiler.StaticRewriteRules
  ( RewriteStrategy(..)
  , staticRewrites
  ) where

import qualified Data.Set as Set

import Agda.Syntax.Internal

import Agda.TypeChecking.Substitute.Class
import Agda.TypeChecking.Monad.Base
import Agda.TypeChecking.Monad.Context
import Agda.TypeChecking.Reduce

data RewriteStrategy = YesStaticRewrites | NoStaticRewrites
  deriving (Eq, Show)

staticRewrites :: forall m. (MonadReduce m, MonadAddContext m)
               => RewriteStrategy -> Term -> m Term
staticRewrites NoStaticRewrites t = pure t
staticRewrites rewr t = goTerm t where

  goTerm  :: Term -> m Term
  -- TODO: propagate more type information if needed
  goTerm (Lam info body) = do
    let x = absName body
    Lam info . mkAbs x <$> addContext x (goTerm (absBody body))
  goTerm (Def q es) = do
    es <- goElims es
    locallyReduceDefs (OnlyReduceDefs (Set.singleton q)) $
      reduce (Def q es)
  goTerm (Con c info es) = do
    es <- goElims es
    locallyReduceDefs (OnlyReduceDefs (Set.singleton (conName c))) $
      reduce (Con c info es)
  goTerm (MetaV id es) = MetaV id <$> goElims es
  goTerm (Dummy str es) = Dummy str <$> goElims es
  goTerm v = pure v

  goElims :: Elims -> m Elims
  goElims = traverse (traverse goTerm)
