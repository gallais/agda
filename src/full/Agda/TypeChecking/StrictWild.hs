module Agda.TypeChecking.StrictWild
       ( WildSplit(..)
       , wildSplit
       ) where

import qualified Agda.Syntax.Abstract as A
import Agda.Syntax.Common
import Agda.Syntax.Info
import Agda.Syntax.Internal

import Agda.TypeChecking.Monad
import Agda.TypeChecking.Monad.Builtin
import Agda.TypeChecking.Coverage
import Agda.TypeChecking.Constraints
import Agda.TypeChecking.Datatypes
import Agda.TypeChecking.Records
import Agda.TypeChecking.Reduce
import Agda.TypeChecking.Substitute
import Agda.TypeChecking.Telescope

import Agda.Utils.Except ( MonadError )
import Agda.Utils.Impossible
import Agda.Utils.List

-- | Reduce a type and check whether it is a datatype or a record.
--   Succeeds only if type is not blocked by a meta var.
tryDataOrRecordType :: ( MonadTCM tcm, MonadReduce tcm
                       , HasConstInfo tcm, HasBuiltins tcm
                       )
                    => Type -> tcm (Maybe (DataOrRecord, QName))
tryDataOrRecordType t = ifBlocked t (\ _ _ -> pure Nothing) $ \ _ t -> do
  case unEl t of
    Def r es -> do
      dr <- liftTCM $ isDataOrRecordType r
      pure $ (,r) <$> dr
    _ -> pure Nothing

data WildSplit
  = NoSplit          -- ^ Type cannot be split (coinductive, multiple constructor candidates, etc.)
  | DataSplit QName  -- ^ Data type together with name of the irrefutable constructor (split & stop)
  | RecordSplit      -- ^ Record split (use constructor and continue splitting recursively)

wildSplit :: ( MonadTCM tcm, MonadReduce tcm, MonadError TCErr tcm
             , HasConstInfo tcm, HasBuiltins tcm
             )
          => Type -> tcm WildSplit
wildSplit t = tryDataOrRecordType t >>= \case
  Nothing             -> pure NoSplit

  -- If we have a record, we check whether it is (co)inductive or not
  Just (IsRecord, qn) -> do
    def <- getRecordDef qn
    pure $ case recInduction def of
      Nothing          -> RecordSplit
      Just Inductive   -> DataSplit (conName $ recConHead def)
      Just CoInductive -> NoSplit

  Just (IsData, _) -> do

    -- from the current context xs:ts, create a pattern list
    -- xs _ : ts t and try to split on _ (the last variable)

    tel0 <- getContextTelescope
    let gamma = telToList tel0 ++ [domFromArg $ defaultArg (underscore, t)]
        tel   = telFromList gamma
        ps    = teleNamedArgs tel

    dontAssignMetas $ liftTCM (splitLast Inductive tel ps) >>= \case

      Left NotADatatype{} -> __IMPOSSIBLE__
      Left _              -> pure NoSplit -- gentle failure
      Right cov -> caseSingleton (splitClauses cov) (pure NoSplit) $ \ cl ->
        case namedArg $ last $ scPats cl of
          ConP c _ _ -> pure (DataSplit (conName c))
          _          -> __IMPOSSIBLE__
