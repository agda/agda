
{-| To enable separate type checking, an interface file is created for each
    file that has been type checked. When type checking an import we can simply
    read the interface file, instead of repeating the type checking.
-}
module Syntax.Interface where

import Syntax.Common

data Interface =
	Interface   { moduleName	:: QName
		    , arity		:: Arity
		    , definedNames	:: [Name]
		    , constructorNames	:: [Name]
		    , datatypeNames	:: [Name]
		    , subModules	:: [Interface]
			-- ^ names of sub-modules are not fully qualified
		    -- here should go types and definitions
		    }
    deriving (Show)

{-

How to treat submodules?
    sub-interfaces? yes

-}

