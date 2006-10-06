
module TypeChecking.Interface where

import Syntax.Scope
import Syntax.Abstract.Name
import TypeChecking.Monad

type InterfaceVersion = (Char, Char, Char, Char, Char, Char)

currentInterfaceVersion :: (Char, Char, Char, Char, Char, Char)
currentInterfaceVersion = ('A','I','1','.','0','1')

data Interface = Interface
	{ iVersion	   :: InterfaceVersion
	, iImportedModules :: [ModuleName]
	, iScope	   :: ModuleScope
	, iSignature	   :: Signature
	, iImports	   :: Signature
	, iBuiltin	   :: BuiltinThings String
	}

