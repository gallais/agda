module Agda.TypeChecking.StrictWild where

import Agda.TypeChecking.Monad.Base
import Agda.TypeChecking.Monad.Builtin
import Agda.TypeChecking.Monad.Signature

import Agda.Syntax.Internal
import Agda.Utils.Except ( MonadError )

data WildSplit
  = NoSplit          -- ^ Type cannot be split (coinductive, multiple constructor candidates, etc.)
  | DataSplit QName  -- ^ Data type together with name of the irrefutable constructor (split & stop)
  | RecordSplit      -- ^ Record split (use constructor and continue splitting recursively)

wildSplit :: ( MonadTCM tcm, MonadReduce tcm, MonadError TCErr tcm
             , HasConstInfo tcm, HasBuiltins tcm
             )
          => Type -> tcm WildSplit
