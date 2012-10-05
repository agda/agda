{-# LANGUAGE DeriveDataTypeable, StandaloneDeriving, FlexibleContexts, UndecidableInstances #-}
{-| An info object contains additional information about a piece of abstract
    syntax that isn't part of the actual syntax. For instance, it might contain
    the source code posisiton of an expression or the concrete syntax that
    an internal expression originates from.
-}

module Agda.Syntax.Info where

import Data.Typeable (Typeable)
import Text.Show.Functions

import qualified Agda.Syntax.Concrete.Name as C
import Agda.Syntax.Common
import Agda.Syntax.Position
import Agda.Syntax.Concrete
import Agda.Syntax.Fixity
import Agda.Syntax.Scope.Base (ScopeInfo, emptyScopeInfo)

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
                 , metaNameSuggestion :: String
		 }
  deriving (Typeable, Show)

emptyMetaInfo :: MetaInfo
emptyMetaInfo = MetaInfo
  { metaRange          = noRange
  , metaScope          = emptyScopeInfo
  , metaNumber         = Nothing
  , metaNameSuggestion = ""
  }

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
  deriving (Typeable, Show)

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
  deriving (Typeable)

deriving instance (Show OpenShortHand, Show ImportDirective) => Show ModuleInfo

instance HasRange ModuleInfo where
  getRange = minfoRange

instance SetRange ModuleInfo where
  setRange r i = i { minfoRange = r }

instance KillRange ModuleInfo where
  killRange m = m { minfoRange = killRange $ minfoRange m }

---------------------------------------------------------------------------
-- Let info
---------------------------------------------------------------------------

newtype LetInfo = LetRange Range
  deriving (Typeable, Show)

instance HasRange LetInfo where
  getRange (LetRange r)   = r

instance KillRange LetInfo where
  killRange (LetRange r) = LetRange (killRange r)

{--------------------------------------------------------------------------
    Definition information (declarations that actually define something)
 --------------------------------------------------------------------------}

data DefInfo =
	DefInfo	{ defFixity   :: Fixity'
		, defAccess   :: Access
		, defAbstract :: IsAbstract
		, defInfo     :: DeclInfo
		}
  deriving (Typeable, Show)

mkDefInfo :: Name -> Fixity' -> Access -> IsAbstract -> Range -> DefInfo
mkDefInfo x f a ab r = DefInfo f a ab (DeclInfo x r)

instance HasRange DefInfo where
  getRange = getRange . defInfo

instance SetRange DefInfo where
  setRange r i = i { defInfo = setRange r (defInfo i) }

instance KillRange DefInfo where
  killRange i = i { defInfo = killRange $ defInfo i }

{--------------------------------------------------------------------------
    General declaration information
 --------------------------------------------------------------------------}

data DeclInfo =
	DeclInfo { declName  :: Name
		 , declRange :: Range
		 }
  deriving (Typeable, Show)

instance HasRange DeclInfo where
  getRange = declRange

instance SetRange DeclInfo where
  setRange r i = i { declRange = r }

instance KillRange DeclInfo where
  killRange i = i { declRange = killRange $ declRange i }

{--------------------------------------------------------------------------
    Mutual block information
 --------------------------------------------------------------------------}

data MutualInfo =
     MutualInfo { mutualTermCheck :: Bool  -- ^ termination check (default=True)
		, mutualRange     :: Range
		}
  deriving (Typeable, Show)

instance HasRange MutualInfo where
  getRange = mutualRange

instance KillRange MutualInfo where
  killRange i = i { mutualRange = killRange $ mutualRange i }

{--------------------------------------------------------------------------
    Left hand side information
 --------------------------------------------------------------------------}

newtype LHSInfo = LHSRange Range
  deriving (Typeable, Show)

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
  deriving (Typeable)

instance Show PatInfo where
  show (PatRange r) = "PatRange " ++ show r
  show (PatSource r _) = "PatSource " ++ show r

instance HasRange PatInfo where
  getRange (PatRange r)    = r
  getRange (PatSource r _) = r

instance KillRange PatInfo where
  killRange (PatRange r)    = PatRange $ killRange r
  killRange (PatSource r f) = PatSource (killRange r) f
