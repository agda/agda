{-# LANGUAGE DeriveDataTypeable, StandaloneDeriving, FlexibleContexts, UndecidableInstances #-}
{-| An info object contains additional information about a piece of abstract
    syntax that isn't part of the actual syntax. For instance, it might contain
    the source code posisiton of an expression or the concrete syntax that
    an internal expression originates from.
-}

module Agda.Syntax.Info where

import Data.Generics (Typeable, Data)
import Text.Show.Functions

import qualified Agda.Syntax.Concrete.Name as C
import Agda.Syntax.Common
import Agda.Syntax.Position
import Agda.Syntax.Concrete
import Agda.Syntax.Fixity
import Agda.Syntax.Scope.Base (ScopeInfo)

{--------------------------------------------------------------------------
    No information
 --------------------------------------------------------------------------}

data Info = Nope

{--------------------------------------------------------------------------
    Meta information
 --------------------------------------------------------------------------}

data MetaInfo =
	MetaInfo { metaRange	:: Range
		 , metaScope	:: ScopeInfo
		 , metaNumber	:: Maybe Nat
		 }
  deriving (Typeable, Data, Show)

instance HasRange MetaInfo where
  getRange = metaRange

instance KillRange MetaInfo where
  killRange m = m { metaRange = killRange $ metaRange m }

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
  deriving (Typeable, Data, Show)

instance HasRange ExprInfo where
  getRange (ExprRange  r  ) = r
  getRange (ExprSource r _) = r

instance KillRange ExprInfo where
  killRange (ExprRange r)    = ExprRange (killRange r)
  killRange (ExprSource r f) = ExprSource (killRange r) f

{--------------------------------------------------------------------------
    Module information
 --------------------------------------------------------------------------}

data ModuleInfo =
	ModuleInfo { minfoRange    :: Range
                   , minfoAsTo     :: Range
                     -- The range of the \"as\" and \"to\" keywords,
                     -- if any. Retained for highlighting purposes.
                   , minfoAsName   :: Maybe C.Name
                     -- The \"as\" module name, if any. Retained for
                     -- highlighting purposes.
                   , minfoOpenShort :: Maybe OpenShortHand
                   , minfoDirective :: Maybe ImportDirective
                     -- Retained for abstractToConcrete of ModuleMacro
		   }
  deriving (Typeable, Data)

deriving instance (Show OpenShortHand, Show ImportDirective) => Show ModuleInfo

instance HasRange ModuleInfo where
  getRange = minfoRange

instance KillRange ModuleInfo where
  killRange m = m { minfoRange = killRange $ minfoRange m }

---------------------------------------------------------------------------
-- Let info
---------------------------------------------------------------------------

newtype LetInfo = LetRange Range
  deriving (Typeable, Data, Show)

instance HasRange LetInfo where
  getRange (LetRange r)   = r

instance KillRange LetInfo where
  killRange (LetRange r) = LetRange (killRange r)

{--------------------------------------------------------------------------
    Definition information (declarations that actually defines something)
 --------------------------------------------------------------------------}

data DefInfo =
	DefInfo	{ defFixity   :: Fixity
		, defAccess   :: Access
		, defAbstract :: IsAbstract
		, defInfo     :: DeclInfo
		}
  deriving (Typeable, Data, Show)

mkDefInfo :: Name -> Fixity -> Access -> IsAbstract -> Range -> DefInfo
mkDefInfo x f a ab r = DefInfo f a ab (DeclInfo x r)

instance HasRange DefInfo where
  getRange = getRange . defInfo

instance KillRange DefInfo where
  killRange i = i { defInfo = killRange $ defInfo i }

{--------------------------------------------------------------------------
    General declaration information
 --------------------------------------------------------------------------}

data DeclInfo =
	DeclInfo { declName  :: Name
		 , declRange :: Range
		 }
  deriving (Typeable, Data, Show)

instance HasRange DeclInfo where
  getRange = declRange

instance KillRange DeclInfo where
  killRange i = i { declRange = killRange $ declRange i }

{--------------------------------------------------------------------------
    Left hand side information
 --------------------------------------------------------------------------}

newtype LHSInfo = LHSRange Range
  deriving (Typeable, Data, Show)

instance HasRange LHSInfo where
  getRange (LHSRange r) = r

instance KillRange LHSInfo where
  killRange (LHSRange r) = LHSRange (killRange r)

{--------------------------------------------------------------------------
    Pattern information
 --------------------------------------------------------------------------}

-- TODO: Is it safe to add Typeable/Data here? PatInfo contains a
-- function space.

data PatInfo = PatRange Range
	     | PatSource Range (Precedence -> Pattern)
  deriving (Typeable, Data)

instance Show PatInfo where
  show (PatRange r) = "PatRange " ++ show r
  show (PatSource r _) = "PatSource " ++ show r

instance HasRange PatInfo where
  getRange (PatRange r)    = r
  getRange (PatSource r _) = r

instance KillRange PatInfo where
  killRange (PatRange r)    = PatRange $ killRange r
  killRange (PatSource r f) = PatSource (killRange r) f

