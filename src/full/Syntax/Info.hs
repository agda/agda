{-# OPTIONS -fglasgow-exts #-}
{-| An info object contains additional information about a piece of abstract
    syntax that isn't part of the actual syntax. For instance, it might contain
    the source code posisiton of an expression or the concrete syntax that
    an internal expression originates from.
-}

module Syntax.Info where

import Syntax.Common
import Syntax.Position
import Syntax.Concrete
import Syntax.Concrete.Pretty () -- TODO: only needed for deriving Show for PatInfo
import Syntax.Scope

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
    deriving (Show)

instance HasRange NameInfo where
    getRange = getRange . concreteName

{--------------------------------------------------------------------------
    Meta information
 --------------------------------------------------------------------------}

data MetaInfo =
	MetaInfo { metaRange	:: Range
		 , metaScope	:: ScopeInfo
		 }
    deriving (Show)

instance HasRange MetaInfo where
    getRange = metaRange

{--------------------------------------------------------------------------
    General expression information
 --------------------------------------------------------------------------}

-- | For a general expression we can either remember just the source code
--   position or the entire concrete expression it came from.
data ExprInfo
	= ExprRange  Range
	| ExprSource Expr
    deriving (Show)

instance HasRange ExprInfo where
    getRange (ExprRange  r) = r
    getRange (ExprSource e) = getRange e


{--------------------------------------------------------------------------
    Definition information (declarations that actually defines somethis)
 --------------------------------------------------------------------------}

data DefInfo =
	DefInfo	{ defFixity :: Fixity
		, defAccess :: Access
		, defInfo   :: DeclInfo
		}
    deriving (Show)

mkRangedDefInfo :: Fixity -> Access -> Range -> DefInfo
mkRangedDefInfo f a r = DefInfo f a (DeclRange r)

mkSourcedDefInfo :: Fixity -> Access -> [Declaration] -> DefInfo
mkSourcedDefInfo f a ds = DefInfo f a (DeclSource ds)

instance HasRange DefInfo where
    getRange = getRange . defInfo

{--------------------------------------------------------------------------
    General declaration information
 --------------------------------------------------------------------------}

data DeclInfo
	= DeclRange  Range
	| DeclSource [Declaration]
    deriving (Show)

instance HasRange DeclInfo where
    getRange (DeclRange  r)  = r
    getRange (DeclSource ds) = getRange ds


{--------------------------------------------------------------------------
    Left hand side information
 --------------------------------------------------------------------------}

data LHSInfo = LHSSource LHS
    deriving (Show)

instance HasRange LHSInfo where
    getRange (LHSSource lhs) = getRange lhs


{--------------------------------------------------------------------------
    Pattern information
 --------------------------------------------------------------------------}

data PatInfo = PatRange Range
	     | PatSource Pattern
    deriving (Show)

instance HasRange PatInfo where
    getRange (PatRange r)  = r
    getRange (PatSource p) = getRange p

