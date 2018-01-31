{-# LANGUAGE CPP #-}

module Agda.TypeChecking.Warnings where

import qualified Data.Set as Set
import qualified Data.List as List
import Data.Maybe ( catMaybes )

import Control.Monad (guard, forM_)

import Agda.Interaction.Options
import Agda.Interaction.Options.Warnings

import Agda.Syntax.Common
import Agda.Syntax.Concrete.Definitions (DeclarationWarning(..))
import Agda.Syntax.Position
import Agda.Syntax.Parser

import {-# SOURCE #-} Agda.TypeChecking.Errors
import Agda.TypeChecking.Monad.Base
import Agda.TypeChecking.Monad.Constraints
import Agda.TypeChecking.Monad.MetaVars
import {-# SOURCE #-} Agda.TypeChecking.Pretty

import Agda.Utils.Lens
import qualified Agda.Utils.Pretty as P
import Agda.Utils.Except

{-# SPECIALIZE genericWarning :: P.Doc -> TCM () #-}
genericWarning :: MonadTCM tcm => P.Doc -> tcm ()
genericWarning = warning . GenericWarning

{-# SPECIALIZE genericNonFatalError :: P.Doc -> TCM () #-}
genericNonFatalError :: MonadTCM tcm => P.Doc -> tcm ()
genericNonFatalError = warning . GenericNonFatalError

{-# SPECIALIZE warning_ :: Warning -> TCM TCWarning #-}
warning_ :: MonadTCM tcm => Warning -> tcm TCWarning
warning_ w = do
  r <- view eRange
  c <- view eCall
  -- NicifierIssues print their own error locations in their list of
  -- issues (but we might need to keep the overall range `r` for
  -- comparing ranges)
  let r' = case w of { NicifierIssue{} -> NoRange ; _ -> r }
  p <- liftTCM $ sayWhen r' c $ prettyWarning w
  liftTCM $ return $ TCWarning r w p

-- | @applyWarningMode@ filters out the warnings the user has not requested
-- Users are not allowed to ignore non-fatal errors.

applyWarningMode :: WarningMode -> Warning -> Maybe Warning
applyWarningMode wm w = case classifyWarning w of
  ErrorWarnings -> Just w
  AllWarnings   -> w <$ guard (Set.member (warningName w) $ wm ^. warningSet)

{-# SPECIALIZE warnings :: [Warning] -> TCM () #-}
warnings :: MonadTCM tcm => [Warning] -> tcm ()
warnings ws = do

  wmode <- optWarningMode <$> pragmaOptions

  let add w tcwarn tcwarns
        | onlyOnce w && elem tcwarn tcwarns = tcwarns -- Eq on TCWarning only checks head constructor
        | otherwise                         = tcwarn : tcwarns

  forM_ (catMaybes $ applyWarningMode wmode <$> ws) $ \ w' -> do
    tcwarn <- warning_ w'
    if wmode ^. warn2Error
    then typeError $ NonFatalErrors [tcwarn]
    else stTCWarnings %= add w' tcwarn

{-# SPECIALIZE warning :: Warning -> TCM () #-}
warning :: MonadTCM tcm => Warning -> tcm ()
warning = warnings . pure


-- | Classifying warnings: some are benign, others are (non-fatal) errors

data WhichWarnings =
    ErrorWarnings -- ^ warnings that will be turned into errors
  | AllWarnings   -- ^ all warnings, including errors and benign ones
  -- Note: order of constructors is important for the derived Ord instance
  deriving (Eq, Ord)

isUnsolvedWarning :: Warning -> Bool
isUnsolvedWarning w = case w of
  UnsolvedMetaVariables{}    -> True
  UnsolvedInteractionMetas{} -> True
  UnsolvedConstraints{}      -> True
 -- rest
  _                          -> False

classifyWarning :: Warning -> WhichWarnings
classifyWarning w = case w of
  OldBuiltin{}               -> AllWarnings
  EmptyRewritePragma         -> AllWarnings
  UselessPublic              -> AllWarnings
  UnreachableClauses{}       -> AllWarnings
  UselessInline{}            -> AllWarnings
  GenericWarning{}           -> AllWarnings
  DeprecationWarning{}       -> AllWarnings
  NicifierIssue{}            -> AllWarnings
  InversionDepthReached{}    -> AllWarnings
  TerminationIssue{}         -> ErrorWarnings
  CoverageIssue{}            -> ErrorWarnings
  CoverageNoExactSplit{}     -> ErrorWarnings
  NotStrictlyPositive{}      -> ErrorWarnings
  UnsolvedMetaVariables{}    -> ErrorWarnings
  UnsolvedInteractionMetas{} -> ErrorWarnings
  UnsolvedConstraints{}      -> ErrorWarnings
  GenericNonFatalError{}     -> ErrorWarnings
  SafeFlagPostulate{}        -> ErrorWarnings
  SafeFlagPragma{}           -> ErrorWarnings
  SafeFlagNonTerminating     -> ErrorWarnings
  SafeFlagTerminating        -> ErrorWarnings
  SafeFlagPrimTrustMe        -> ErrorWarnings
  SafeFlagNoPositivityCheck  -> ErrorWarnings
  SafeFlagPolarity           -> ErrorWarnings
  ParseWarning{}             -> ErrorWarnings

-- | Should we only emit a single warning with this constructor.
onlyOnce :: Warning -> Bool
onlyOnce InversionDepthReached{} = True
onlyOnce _ = False

classifyWarnings :: [TCWarning] -> ([TCWarning], [TCWarning])
classifyWarnings = List.partition $ (< AllWarnings) . classifyWarning . tcWarning

-- | running the Parse monad

runPM :: PM a -> TCM a
runPM m = do
  (res, ws) <- runPMIO m
  mapM_ (warning . ParseWarning) ws
  case res of
    Left  e -> throwError (Exception (getRange e) (P.pretty e))
    Right a -> return a

-- | Collect all warnings that have accumulated in the state.
-- Depending on the argument, we either respect the flags passed
-- in by the user, or not (for instance when deciding if we are
-- writing an interface file or not)

getUniqueMetasRanges :: [MetaId] -> TCM [Range]
getUniqueMetasRanges = fmap List.nub . mapM getMetaRange

getUnsolvedMetas :: TCM [Range]
getUnsolvedMetas = do
  openMetas            <- getOpenMetas
  interactionMetas     <- getInteractionMetas
  getUniqueMetasRanges (openMetas List.\\ interactionMetas)

getAllUnsolved :: TCM [TCWarning]
getAllUnsolved = do
  unsolvedInteractions <- getUniqueMetasRanges =<< getInteractionMetas
  unsolvedConstraints  <- getAllConstraints
  unsolvedMetas        <- getUnsolvedMetas

  let checkNonEmpty c rs = c rs <$ guard (not $ null rs)

  mapM warning_ $ catMaybes
                [ checkNonEmpty UnsolvedInteractionMetas unsolvedInteractions
                , checkNonEmpty UnsolvedMetaVariables    unsolvedMetas
                , checkNonEmpty UnsolvedConstraints      unsolvedConstraints ]

getAllWarnings' :: WhichWarnings -> IgnoreFlags -> TCM [TCWarning]
getAllWarnings' ww ifs = do
  unsolved            <- getAllUnsolved
  collectedTCWarnings <- use stTCWarnings

  fmap (filter ((<= ww) . classifyWarning . tcWarning))
    $ applyFlagsToTCWarnings ifs $ reverse
    $ unsolved ++ collectedTCWarnings


-- | Depending which flags are set, one may happily ignore some
-- warnings.

applyFlagsToTCWarnings :: IgnoreFlags -> [TCWarning] -> TCM [TCWarning]
applyFlagsToTCWarnings ifs ws = do

  -- For some reason some SafeFlagPragma seem to be created multiple times.
  -- This is a way to collect all of them and remove duplicates.
  let pragmas w = case tcWarning w of { SafeFlagPragma ps -> ([w], ps); _ -> ([], []) }
  let sfp = case fmap List.nub (foldMap pragmas ws) of
              (TCWarning r w p:_, sfp) ->
                 [TCWarning r (SafeFlagPragma sfp) p]
              _                        -> []


  unsolvedNotOK <- not . optAllowUnsolved <$> pragmaOptions
  negativeNotOK <- not . optDisablePositivity <$> pragmaOptions
  loopingNotOK  <- optTerminationCheck <$> pragmaOptions
  catchallNotOK <- optExactSplit <$> pragmaOptions

  -- filter out the warnings the flags told us to ignore
  let cleanUp w =
        let ignore = ifs == IgnoreFlags
            keepUnsolved us = not (null us) && (ignore || unsolvedNotOK)
        in case w of
          TerminationIssue{}           -> ignore || loopingNotOK
          CoverageIssue{}              -> ignore || unsolvedNotOK
          NotStrictlyPositive{}        -> ignore || negativeNotOK
          UnsolvedMetaVariables ums    -> keepUnsolved ums
          UnsolvedInteractionMetas uis -> keepUnsolved uis
          UnsolvedConstraints ucs      -> keepUnsolved ucs
          OldBuiltin{}                 -> True
          EmptyRewritePragma           -> True
          UselessPublic                -> True
          ParseWarning{}               -> True
          UnreachableClauses{}         -> True
          InversionDepthReached{}      -> True
          CoverageNoExactSplit{}       -> catchallNotOK
          UselessInline{}              -> True
          GenericWarning{}             -> True
          GenericNonFatalError{}       -> True
          SafeFlagPostulate{}          -> True
          SafeFlagPragma{}             -> False -- dealt with separately
          SafeFlagNonTerminating       -> True
          SafeFlagTerminating          -> True
          SafeFlagPrimTrustMe          -> True
          SafeFlagNoPositivityCheck    -> True
          SafeFlagPolarity             -> True
          DeprecationWarning{}         -> True
          NicifierIssue{}              -> True

  return $ sfp ++ filter (cleanUp . tcWarning) ws
