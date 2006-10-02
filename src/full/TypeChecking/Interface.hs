
module TypeChecking.Interface where

import Syntax.Scope
import Syntax.Abstract.Name
import TypeChecking.Monad

data Interface = Interface
	{ iImportedModules :: [ModuleName]
	, iScope	   :: ModuleScope
	, iSignature	   :: Signature
	, iImports	   :: Signature
	, iBuiltin	   :: BuiltinThings String
	}

