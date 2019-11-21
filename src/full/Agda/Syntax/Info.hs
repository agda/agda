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

import qualified Agda.Syntax.Concrete.Name as C
import Agda.Syntax.Common
import Agda.Syntax.Position
import Agda.Syntax.Concrete
import Agda.Syntax.Fixity
import Agda.Syntax.Scope.Base (ScopeInfo, emptyScopeInfo)

import Agda.Utils.Function
import Agda.Utils.Functor
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
  deriving (Data, Show, Eq)

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
  deriving (Data, Show, Eq, Null)

exprNoRange :: ExprInfo
exprNoRange = ExprRange noRange

instance HasRange ExprInfo where
  getRange (ExprRange r) = r

instance KillRange ExprInfo where
  killRange (ExprRange r) = exprNoRange

{--------------------------------------------------------------------------
    Application information
 --------------------------------------------------------------------------}

-- | Information about application
data AppInfo = AppInfo
  { appRange  :: Range
  , appOrigin :: Origin
  , appParens :: ParenPreference -- ^ Do we prefer a appbda argument with or without parens?
  }
  deriving (Data, Show, Eq, Ord)

-- | Default is system inserted and prefer parens.
defaultAppInfo :: Range -> AppInfo
defaultAppInfo r = AppInfo{ appRange = r, appOrigin = Inserted, appParens = PreferParen }

-- | `AppInfo` with no range information.
defaultAppInfo_ :: AppInfo
defaultAppInfo_ = defaultAppInfo noRange

instance HasRange AppInfo where
  getRange = appRange

instance KillRange AppInfo where
  killRange (AppInfo r o p) = AppInfo (killRange r) o p

instance LensOrigin AppInfo where
  getOrigin = appOrigin
  mapOrigin f i = i { appOrigin = f (appOrigin i) }

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
  deriving (Data, Eq, Show)

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
  deriving (Data, Show, Eq, Null)

instance HasRange LetInfo where
  getRange (LetRange r)   = r

instance KillRange LetInfo where
  killRange (LetRange r) = LetRange noRange

{--------------------------------------------------------------------------
    Definition information (declarations that actually define something)
 --------------------------------------------------------------------------}

data DefInfo' t = DefInfo
  { defFixity   :: Fixity'
  , defAccess   :: Access
  , defAbstract :: IsAbstract
  , defInstance :: IsInstance
  , defMacro    :: IsMacro
  , defInfo     :: DeclInfo
  , defTactic   :: Maybe t
  }
  deriving (Data, Show, Eq)

mkDefInfo :: Name -> Fixity' -> Access -> IsAbstract -> Range -> DefInfo' t
mkDefInfo x f a ab r = DefInfo f a ab NotInstanceDef NotMacroDef (DeclInfo x r) Nothing

-- | Same as @mkDefInfo@ but where we can also give the @IsInstance@
mkDefInfoInstance :: Name -> Fixity' -> Access -> IsAbstract -> IsInstance -> IsMacro -> Range -> DefInfo' t
mkDefInfoInstance x f a ab i m r = DefInfo f a ab i m (DeclInfo x r) Nothing

instance HasRange (DefInfo' t) where
  getRange = getRange . defInfo

instance SetRange (DefInfo' t) where
  setRange r i = i { defInfo = setRange r (defInfo i) }

instance KillRange t => KillRange (DefInfo' t) where
  killRange i = i { defInfo   = killRange $ defInfo i,
                    defTactic = killRange $ defTactic i }

instance LensIsAbstract (DefInfo' t) where
  lensIsAbstract f i = (f $! defAbstract i) <&> \ a -> i { defAbstract = a }

instance AnyIsAbstract (DefInfo' t) where
  anyIsAbstract = defAbstract


{--------------------------------------------------------------------------
    General declaration information
 --------------------------------------------------------------------------}

data DeclInfo = DeclInfo
  { declName  :: Name
  , declRange :: Range
  }
  deriving (Data, Show, Eq)

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
  { mutualTerminationCheck :: TerminationCheck Name
  , mutualCoverageCheck    :: CoverageCheck
  , mutualPositivityCheck  :: PositivityCheck
  , mutualRange            :: Range
  }
  deriving (Data, Show, Eq)

-- | Default value for 'MutualInfo'.
instance Null MutualInfo where
  empty = MutualInfo TerminationCheck YesCoverageCheck YesPositivityCheck noRange

instance HasRange MutualInfo where
  getRange = mutualRange

instance KillRange MutualInfo where
  killRange i = i { mutualRange = noRange }

{--------------------------------------------------------------------------
    Left hand side information
 --------------------------------------------------------------------------}

data LHSInfo = LHSInfo
  { lhsRange    :: Range
  , lhsEllipsis :: ExpandedEllipsis
  } deriving (Data, Show, Eq)

instance HasRange LHSInfo where
  getRange (LHSInfo r _) = r

instance KillRange LHSInfo where
  killRange (LHSInfo r ell) = LHSInfo noRange ell

instance Null LHSInfo where
  null i = null (lhsRange i) && null (lhsEllipsis i)
  empty  = LHSInfo empty empty

{--------------------------------------------------------------------------
    Pattern information
 --------------------------------------------------------------------------}

-- | For a general pattern we remember the source code position.
newtype PatInfo
  = PatRange Range
  deriving (Data, Eq, Null, Show, SetRange, HasRange, KillRange)

-- | Empty range for patterns.
patNoRange :: PatInfo
patNoRange = PatRange noRange

-- | Constructor pattern info.
data ConPatInfo = ConPatInfo
  { conPatOrigin   :: ConOrigin
    -- ^ Does this pattern come form the eta-expansion of an implicit pattern?
    ---  Or from a user written constructor or record pattern?
  , conPatInfo     :: PatInfo
  , conPatLazy     :: ConPatLazy
  }
  deriving (Data, Eq, Show)

instance HasRange ConPatInfo where
  getRange = getRange . conPatInfo

instance KillRange ConPatInfo where
  killRange (ConPatInfo b i l) = ConPatInfo b (killRange i) l

instance SetRange ConPatInfo where
  setRange r (ConPatInfo b i l) = ConPatInfo b (PatRange r) l

-- | Has the constructor pattern a dotted (forced) constructor?
data ConPatLazy
  = ConPatLazy   -- ^ Dotted constructor.
  | ConPatEager  -- ^ Ordinary constructor.
  deriving (Data, Eq, Ord, Show, Bounded, Enum)
