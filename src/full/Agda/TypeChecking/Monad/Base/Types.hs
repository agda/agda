-- | Data structures for the type checker.
--
-- Part of "Agda.TypeChecking.Monad.Base", extracted to avoid import cycles.

module Agda.TypeChecking.Monad.Base.Types where

import Agda.Syntax.Internal

---------------------------------------------------------------------------
-- ** Context
---------------------------------------------------------------------------

-- | The @Context@ is a stack of 'ContextEntry's.
type Context      = [ContextEntry]
type ContextEntry = Dom (Name, Type)

-- Feel free to move more types from Agda.TypeChecking.Monad.Base here when needed...
