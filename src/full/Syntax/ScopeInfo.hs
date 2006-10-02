{-# OPTIONS -fglasgow-exts #-}

module Syntax.ScopeInfo where

import Data.Generics (Typeable, Data)
import Data.Map as Map

import Syntax.Common
import Syntax.Abstract.Name as AName
import Syntax.Concrete.Name as CName
import Syntax.Fixity

---------------------------------------------------------------------------
-- * Scope
---------------------------------------------------------------------------

-- | A concrete name can be either a bound variable, a defined name (function,
--   constructor or datatype name) or unknown. 'resolve'ing a name gives you one
--   of these.
data ResolvedName
	= VarName AName.Name
	| DefName DefinedName
	| UnknownName
    deriving (Show)

-- | A defined name carries some extra information, such as whether it's private
--   or public and what fixity it has.
data DefinedName =
	DefinedName { access	 :: Access
		    , kindOfName :: KindOfName
		    , fixity	 :: Fixity
		    , theName	 :: AName.QName
		    }
    deriving (Data,Typeable,Show)

{-| There are three kinds of defined names: function names, constructor names,
    and datatype names. It's probably a good idea to single out constructor
    names, but it's not clear that differentiating between function names and
    datatype names gives us anything. One could also imagining distinguishing
    between names of defined functions and names of postulates. One possible
    application of these fine-grained names is to have the interactive system
    color different kinds of names in pretty colors.

    At the moment we only distinguish between constructor names and other
    names, though.
-}
data KindOfName = FunName   -- ^ also includes datatypes
		| ConName
    deriving (Eq, Show,Typeable,Data)

-- | In addition to the names a module contains (which are stored in the
--   'NameSpace') we need to keep track of the arity of a module and whether
--   it is private or public.
data ModuleScope	=
	ModuleScope { moduleArity	:: Arity
		    , moduleAccess	:: Access
		    , moduleContents	:: NameSpace
		    }
    deriving (Show,Typeable,Data)

-- | When you 'resolveModule', this is what you get back.
data ResolvedModule
	= ModuleName ModuleScope
	| UnknownModule

-- | The value in the map is the binding occurence of a variable, so care should
--   be taken to update the 'Range' to the actual occurence. The 'Range' of the
--   binding occurence should be stored in the 'Syntax.Info.NameInfo'.
type LocalVariables = Map CName.Name AName.Name

type Modules	    = Map CName.Name ModuleScope
type DefinedNames   = Map CName.Name DefinedName

{-| A name space is a collection of names (defined names and module names). It
    also has a name of its own. The name is used when recomputing canonical
    names for implicit module declarations (which creates new names rather than
    new ways of referring to things). It is also used for error messages.
-}
data NameSpace =
	NSpace	{ moduleName	:: AName.ModuleName
		, definedNames	:: DefinedNames
		, modules	:: Modules
		}
    deriving (Data,Typeable,Show)

{-| The @privateNameSpace@ and the @publicNameSpace@ don't clash. The reason
    for separating the private and the public name space is that when we leave
    the current module we should pack it up in a 'ModuleScope' containing only
    the public stuff.

    Imported modules go in the private namespace since they aren't visible
    outside a module.

    We keep track of the @contextPrecedence@ for the holes. When inserting
    something into a hole we need to know whether it needs brackets or not.
-}
data ScopeInfo = ScopeInfo
	{ publicNameSpace   :: NameSpace
	, privateNameSpace  :: NameSpace
	, importedModules   :: Modules
	, localVariables    :: LocalVariables
	, contextPrecedence :: Precedence
	}
   deriving (Data,Typeable)

emptyNameSpace :: AName.ModuleName -> NameSpace
emptyNameSpace x = NSpace { moduleName	 = x
			  , definedNames = Map.empty
			  , modules	 = Map.empty
			  }


emptyScopeInfo :: AName.ModuleName -> ScopeInfo
emptyScopeInfo x = ScopeInfo { publicNameSpace	    = emptyNameSpace x
			     , privateNameSpace	    = emptyNameSpace x
			     , importedModules	    = Map.empty
			     , localVariables	    = Map.empty
			     , contextPrecedence    = TopCtx
			     }

emptyScopeInfo_ :: ScopeInfo
emptyScopeInfo_ = emptyScopeInfo $ mkModuleName $ CName.QName noName_

