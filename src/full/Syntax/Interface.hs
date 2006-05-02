
{-| To enable separate type checking, an interface file is created for each
    file that has been type checked. When type checking an import we can simply
    read the interface file, instead of repeating the type checking.
-}
module Syntax.Interface where

import Syntax.Common
import Syntax.Fixity
import Syntax.Abstract.Name

data Interface =
	Interface   { moduleName	:: ModuleName
		    , arity		:: Arity
		    , definedNames	:: [(Name, Fixity)]
		    , constructorNames	:: [(Name, Fixity)]
		    , subModules	:: [Interface]
			-- ^ names of sub-modules are not fully qualified
		    -- here should go types and definitions
		    }
    deriving (Show)

{-

How to treat submodules?
    sub-interfaces? yes

-}

