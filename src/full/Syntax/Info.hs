{-# OPTIONS -fglasgow-exts #-}
{-| An info object contains additional information about a piece of abstract
    syntax that isn't part of the actual syntax. For instance, it might contain
    the source code posisiton of an expression or the concrete syntax that
    an internal expression originates from.
-}

module Syntax.Info where

import Data.Generics(Data,Typeable) 
import Syntax.Common
import Syntax.Position
import Syntax.Concrete
import Syntax.Scope
import Syntax.Fixity

{--------------------------------------------------------------------------
    No information
 --------------------------------------------------------------------------}

data Info = Nope

{--------------------------------------------------------------------------
    Name information
 --------------------------------------------------------------------------}

data NameInfo =
	NameInfo { bindingSite   :: Range
		 , concreteName  :: QName
		 , nameFixity    :: Fixity
		 , nameAccess    :: Access
		 }

instance HasRange NameInfo where
    getRange = getRange . concreteName

{--------------------------------------------------------------------------
    Meta information
 --------------------------------------------------------------------------}

data MetaInfo =
	MetaInfo { metaRange	:: Range
		 , metaScope	:: ScopeInfo
		 }
  deriving (Typeable, Data, Show)

instance HasRange MetaInfo where
    getRange = metaRange

{--------------------------------------------------------------------------
    General expression information
 --------------------------------------------------------------------------}

-- | For a general expression we can either remember just the source code
--   position or the entire concrete expression it came from.
data ExprInfo
	= ExprRange  Range
	| ExprSource Range (Precedence -> Expr)
	    -- ^ Even if we store the original expression we have to know
	    --	 whether to put parenthesis around it.

instance HasRange ExprInfo where
    getRange (ExprRange  r  ) = r
    getRange (ExprSource r _) = r


{--------------------------------------------------------------------------
    Module information
 --------------------------------------------------------------------------}

data ModuleInfo =
	ModuleInfo { minfoAccess :: Access
		   , minfoSource :: DeclSource
		   }

mkRangedModuleInfo :: Access -> Range -> ModuleInfo
mkRangedModuleInfo a r = ModuleInfo a (DeclRange r)

mkSourcedModuleInfo :: Access -> [Declaration] -> ModuleInfo
mkSourcedModuleInfo a ds = ModuleInfo a (DeclSource ds)

instance HasRange ModuleInfo where
    getRange = getRange . minfoSource

{--------------------------------------------------------------------------
    Definition information (declarations that actually defines something)
 --------------------------------------------------------------------------}

data DefInfo =
	DefInfo	{ defFixity   :: Fixity
		, defAccess   :: Access
		, defAbstract :: IsAbstract
		, defInfo     :: DeclInfo
		}

mkRangedDefInfo :: Name -> Fixity -> Access -> IsAbstract -> Range -> DefInfo
mkRangedDefInfo x f a ab r = DefInfo f a ab (DeclInfo x $ DeclRange r)

mkSourcedDefInfo :: Name -> Fixity -> Access -> IsAbstract -> [Declaration] -> DefInfo
mkSourcedDefInfo x f a ab ds = DefInfo f a ab (DeclInfo x $ DeclSource ds)

instance HasRange DefInfo where
    getRange = getRange . defInfo

{--------------------------------------------------------------------------
    General declaration information
 --------------------------------------------------------------------------}

data DeclInfo =
	DeclInfo { declName   :: Name
		 , declSource :: DeclSource
		 }
	deriving (Eq)

data DeclSource
	= DeclRange  Range
	| DeclSource [Declaration]
	deriving (Eq)

instance HasRange DeclInfo where
    getRange = getRange . declSource

instance HasRange DeclSource where
    getRange (DeclRange  r)  = r
    getRange (DeclSource ds) = getRange ds


{--------------------------------------------------------------------------
    Left hand side information
 --------------------------------------------------------------------------}

data LHSInfo = LHSSource LHS

instance HasRange LHSInfo where
    getRange (LHSSource lhs) = getRange lhs


{--------------------------------------------------------------------------
    Pattern information
 --------------------------------------------------------------------------}

data PatInfo = PatRange Range
	     | PatSource Range (Precedence -> Pattern)

instance HasRange PatInfo where
    getRange (PatRange r)  = r
    getRange (PatSource r _) = r

