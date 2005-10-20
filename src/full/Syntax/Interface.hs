
{-| To enable separate type checking, an interface file is created for each
    file that has been type checked. When type checking an import we can simply
    read the interface file, instead of repeating the type checking.
-}
module Syntax.Interface where

import Syntax.Common

data Interface =
	Interface   { definedNames	:: [Name]
		    , constructorNames	:: [Name]
		    , datatypeNames	:: [Name]
		    -- here should go types and definitions
		    }
    deriving (Show)

