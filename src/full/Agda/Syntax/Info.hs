{-# LANGUAGE DeriveDataTypeable         #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

{-| An info object contains additional information about a piece of abstract
    syntax that isn't part of the actual syntax. For instance, it might contain
    the source code position of an expression or the concrete syntax that
    an internal expression originates from.
-}

module Agda.Syntax.Info where

import Prelude hiding (null)

import Data.Data (Data)
import Data.Typeable (Typeable)

import qualified Agda.Syntax.Concrete.Name as C
import Agda.Syntax.Common
import Agda.Syntax.Position
import Agda.Syntax.Concrete
import Agda.Syntax.Fixity
import Agda.Syntax.Scope.Base (ScopeInfo, emptyScopeInfo)

import Agda.Utils.Function
import Agda.Utils.Null

{--------------------------------------------------------------------------
    Meta information
 --------------------------------------------------------------------------}

data MetaInfo = MetaInfo
  { metaRange          :: Range
  , metaScope          :: ScopeInfo
  , metaNumber         :: Maybe MetaId
  , metaNameSuggestion :: String
  }
  deriving (Typeable, Data, Show, Eq)

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
  killRange m = m { metaRange = noRange }

{--------------------------------------------------------------------------
    General expression information
 --------------------------------------------------------------------------}

newtype ExprInfo = ExprRange Range
  deriving (Typeable, Data, Show, Eq, Null)

exprNoRange :: ExprInfo
exprNoRange = ExprRange noRange

instance HasRange ExprInfo where
  getRange (ExprRange r) = r

instance KillRange ExprInfo where
  killRange (ExprRange r) = exprNoRange

{--------------------------------------------------------------------------
    Module information
 --------------------------------------------------------------------------}

data ModuleInfo = ModuleInfo
  { minfoRange    :: Range
  , minfoAsTo     :: Range
    -- ^ The range of the \"as\" and \"to\" keywords,
    -- if any. Retained for highlighting purposes.
  , minfoAsName   :: Maybe C.Name
    -- ^ The \"as\" module name, if any. Retained for highlighting purposes.
  , minfoOpenShort :: Maybe OpenShortHand
  , minfoDirective :: Maybe ImportDirective
    -- ^ Retained for @abstractToConcrete@ of 'ModuleMacro'.
  }
  deriving (Typeable, Data, Eq)

deriving instance Show ModuleInfo

instance HasRange ModuleInfo where
  getRange = minfoRange

instance SetRange ModuleInfo where
  setRange r i = i { minfoRange = r }

instance KillRange ModuleInfo where
  killRange m = m { minfoRange = noRange }

---------------------------------------------------------------------------
-- Let info
---------------------------------------------------------------------------

newtype LetInfo = LetRange Range
  deriving (Typeable, Data, Show, Eq, Null)

instance HasRange LetInfo where
  getRange (LetRange r)   = r

instance KillRange LetInfo where
  killRange (LetRange r) = LetRange noRange

{--------------------------------------------------------------------------
    Definition information (declarations that actually define something)
 --------------------------------------------------------------------------}

data DefInfo = DefInfo
  { defFixity   :: Fixity'
  , defAccess   :: Access
  , defAbstract :: IsAbstract
  , defInstance :: IsInstance
  , defMacro    :: IsMacro
  , defInfo     :: DeclInfo
  }
  deriving (Typeable, Data, Show, Eq)

mkDefInfo :: Name -> Fixity' -> Access -> IsAbstract -> Range -> DefInfo
mkDefInfo x f a ab r = DefInfo f a ab NotInstanceDef NotMacroDef (DeclInfo x r)

-- | Same as @mkDefInfo@ but where we can also give the @IsInstance@
mkDefInfoInstance :: Name -> Fixity' -> Access -> IsAbstract -> IsInstance -> IsMacro -> Range -> DefInfo
mkDefInfoInstance x f a ab i m r = DefInfo f a ab i m (DeclInfo x r)

instance HasRange DefInfo where
  getRange = getRange . defInfo

instance SetRange DefInfo where
  setRange r i = i { defInfo = setRange r (defInfo i) }

instance KillRange DefInfo where
  killRange i = i { defInfo = killRange $ defInfo i }

{--------------------------------------------------------------------------
    General declaration information
 --------------------------------------------------------------------------}

data DeclInfo = DeclInfo
  { declName  :: Name
  , declRange :: Range
  }
  deriving (Typeable, Data, Show, Eq)

instance HasRange DeclInfo where
  getRange = declRange

instance SetRange DeclInfo where
  setRange r i = i { declRange = r }

instance KillRange DeclInfo where
  killRange i = i { declRange = noRange }

{--------------------------------------------------------------------------
    Mutual block information
 --------------------------------------------------------------------------}

data MutualInfo = MutualInfo
  { mutualTermCheck       :: TerminationCheck Name
  , mutualPositivityCheck :: PositivityCheck
  , mutualRange           :: Range
  }
  deriving (Typeable, Data, Show, Eq)

-- | Default value for 'MutualInfo'.
instance Null MutualInfo where
  empty = MutualInfo TerminationCheck True noRange

instance HasRange MutualInfo where
  getRange = mutualRange

instance KillRange MutualInfo where
  killRange i = i { mutualRange = noRange }

{--------------------------------------------------------------------------
    Left hand side information
 --------------------------------------------------------------------------}

newtype LHSInfo = LHSRange Range
  deriving (Typeable, Data, Show, Eq, Null)

instance HasRange LHSInfo where
  getRange (LHSRange r) = r

instance KillRange LHSInfo where
  killRange (LHSRange r) = LHSRange noRange

{--------------------------------------------------------------------------
    Pattern information
 --------------------------------------------------------------------------}

-- | For a general pattern we remember the source code position.
newtype PatInfo
  = PatRange Range
  deriving (Typeable, Data, Eq, Null, Show, HasRange, KillRange)

-- | Empty range for patterns.
patNoRange :: PatInfo
patNoRange = PatRange noRange

-- | Constructor pattern info.
data ConPatInfo = ConPatInfo
  { patOrigin   :: ConOrigin
    -- ^ Does this pattern come form the eta-expansion of an implicit pattern?
    ---  Or from a user written constructor or record pattern?
  , patInfo     :: PatInfo
  }
  deriving (Typeable, Data, Eq)

instance Show ConPatInfo where
  show (ConPatInfo po i) = applyWhen (po == ConOSystem) ("implicit " ++) $ show i

instance HasRange ConPatInfo where
  getRange = getRange . patInfo

instance KillRange ConPatInfo where
  killRange (ConPatInfo b i) = ConPatInfo b $ killRange i

instance SetRange ConPatInfo where
  setRange r (ConPatInfo b i) = ConPatInfo b $ PatRange r
