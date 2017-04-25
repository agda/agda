
module Agda.TypeChecking.RecordPatterns where

import Agda.Syntax.Internal (Clause)
import Agda.TypeChecking.Monad.Base (TCM)

translateRecordPatterns :: Clause -> TCM Clause
