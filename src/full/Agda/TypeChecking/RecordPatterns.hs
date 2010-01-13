
module Agda.TypeChecking.RecordPatterns where

import Agda.Syntax.Internal
import Agda.TypeChecking.Monad

translateRecordPatterns :: MonadTCM tcm => Clause -> tcm Clause
translateRecordPatterns clause = return clause
