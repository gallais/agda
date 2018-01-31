module Agda.TypeChecking.Warnings where

import Agda.TypeChecking.Monad.Base

warning :: MonadTCM tcm => Warning -> tcm ()
