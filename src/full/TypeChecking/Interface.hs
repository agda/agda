
module TypeChecking.Interface where

import Syntax.Scope
import TypeChecking.Monad

data Interface = Interface
	{ iScope     :: ModuleScope
	, iSignature :: Signature
	, iImports   :: Signature
	, iBuiltin   :: BuiltinThings String
	}

