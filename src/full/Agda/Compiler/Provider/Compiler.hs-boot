module Agda.Compiler.Provider.Compiler where

import Data.Map ( Map )
import Agda.Syntax.Abstract ( QName )
import Agda.TypeChecking.Monad.Base

provide :: Interface -> TCM (FilePath, Map QName String)