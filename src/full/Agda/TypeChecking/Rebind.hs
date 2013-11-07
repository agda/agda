-- {-# LANGUAGE CPP #-}

module Agda.TypeChecking.Rebind where

import Agda.Syntax.Internal
import Agda.TypeChecking.Monad

-- | Change 'Bind's to 'NoBind' if the variable is not used in the body.
--   Also normalises the body in the process. Or not. Disabled.
rebindClause :: Clause -> TCM Clause
rebindClause = return
