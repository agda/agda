{-# LANGUAGE CPP #-}
{-# LANGUAGE RecursiveDo #-}
-- {-# LANGUAGE UndecidableInstances #-}  -- ghc >= 8.2, GeneralizedNewtypeDeriving MonadTransControl BlockT

module Agda.TypeChecking.Monad.Base
  ( module Agda.TypeChecking.Monad.Base
  , HasOptions (..)
  , RecordFieldWarning
  ) where

import Prelude hiding (null)

import Control.Applicative hiding (empty)
import qualified Control.Concurrent as C
import Control.DeepSeq
import qualified Control.Exception as E

import qualified Control.Monad.Fail as Fail

import Control.Monad                ( void )
import Control.Monad.Except
import Control.Monad.Fix
import Control.Monad.IO.Class       ( MonadIO(..) )
import Control.Monad.State          ( MonadState(..), modify, StateT(..), runStateT )
import Control.Monad.Reader         ( MonadReader(..), ReaderT(..), runReaderT )
import Control.Monad.Writer         ( WriterT )
import Control.Monad.Trans          ( MonadTrans(..), lift )
import Control.Monad.Trans.Control  ( MonadTransControl(..), liftThrough )
import Control.Monad.Trans.Identity ( IdentityT(..), runIdentityT )
import Control.Monad.Trans.Maybe    ( MaybeT(..) )

import Control.Parallel             ( pseq )

import Data.Array (Ix)
import Data.DList (DList)
import Data.Function (on)
import Data.Int
import Data.IntMap (IntMap)
import qualified Data.IntMap as IntMap
import Data.IntSet (IntSet)
import qualified Data.IntSet as IntSet
import qualified Data.List as List
import Data.Maybe
import Data.Map (Map)
import qualified Data.Map as Map -- hiding (singleton, null, empty)
import Data.Sequence (Seq)
import Data.Set (Set, toList, fromList)
import qualified Data.Set as Set -- hiding (singleton, null, empty)
import Data.HashMap.Strict (HashMap)
import qualified Data.HashMap.Strict as HMap
import qualified Data.HashSet as HashSet
import Data.Hashable
import Data.HashSet (HashSet)
import Data.Semigroup ( Semigroup, (<>)) --, Any(..) )
import Data.Set (Set)
import qualified Data.Set as Set
import Data.String
import Data.Text (Text)
import qualified Data.Text.Lazy as TL

import Data.IORef

import GHC.Generics (Generic)

import System.IO (hFlush, stdout)

import Agda.Benchmarking (Benchmark, Phase)

import {-# SOURCE #-} Agda.Compiler.Treeless.Pretty () -- Instances only
import Agda.Syntax.Common
import Agda.Syntax.Builtin (SomeBuiltin, BuiltinId, PrimitiveId)
import qualified Agda.Syntax.Concrete as C
import Agda.Syntax.Concrete.Definitions
  (NiceDeclaration, DeclarationWarning, declarationWarningName)
import qualified Agda.Syntax.Abstract as A
import Agda.Syntax.Internal as I
import Agda.Syntax.Internal.MetaVars
import Agda.Syntax.Internal.Generic (TermLike(..))
import Agda.Syntax.Parser (ParseWarning)
import Agda.Syntax.Parser.Monad (parseWarningName)
import Agda.Syntax.TopLevelModuleName
  (RawTopLevelModuleName, TopLevelModuleName)
import Agda.Syntax.Treeless (Compiled)
import Agda.Syntax.Notation
import Agda.Syntax.Position
import Agda.Syntax.Scope.Base
import qualified Agda.Syntax.Info as Info

import qualified Agda.TypeChecking.Monad.Base.Warning as W
import           Agda.TypeChecking.Monad.Base.Warning (RecordFieldWarning)

import Agda.TypeChecking.CompiledClause
import Agda.TypeChecking.Coverage.SplitTree
import Agda.TypeChecking.Positivity.Occurrence
import Agda.TypeChecking.Free.Lazy (Free(freeVars'), underBinder', underBinder)

import Agda.Termination.TypeBased.Syntax ( SizeSignature )

import Agda.Compiler.Backend.Base

import Agda.Interaction.Options
import Agda.Interaction.Options.Warnings
import Agda.Interaction.Response.Base (Response_boot(..))
import Agda.Interaction.Highlighting.Precise
  (HighlightingInfo, NameKind)
import Agda.Interaction.Library

import Agda.Utils.Benchmark (MonadBench(..))
import Agda.Utils.BiMap (BiMap, HasTag(..))
import qualified Agda.Utils.BiMap as BiMap
import Agda.Utils.CallStack ( CallStack, HasCallStack, withCallerCallStack )
import Agda.Utils.FileName
import Agda.Utils.Functor
import Agda.Utils.Hash
import Agda.Utils.Lens
import Agda.Utils.List
import Agda.Utils.ListT
import Agda.Utils.List1 (List1, pattern (:|))
import Agda.Utils.List2 (List2, pattern List2)
import qualified Agda.Utils.List1 as List1
import qualified Agda.Utils.Maybe.Strict as Strict
import Agda.Utils.Monad
import Agda.Utils.Null
import Agda.Utils.Permutation
import Agda.Syntax.Common.Pretty
import Agda.Utils.Singleton
import Agda.Utils.SmallSet (SmallSet)
import qualified Agda.Utils.SmallSet as SmallSet
import Agda.Utils.Update

import Agda.Utils.Impossible

---------------------------------------------------------------------------
-- * Type checking state
---------------------------------------------------------------------------

data TCState = TCSt
  { stPreScopeState   :: !PreScopeState
    -- ^ The state which is frozen after scope checking.
  , stPostScopeState  :: !PostScopeState
    -- ^ The state which is modified after scope checking.
  , stPersistentState :: !PersistentTCState
    -- ^ State which is forever, like a diamond.
  }
  deriving Generic

class Monad m => ReadTCState m where
  getTCState :: m TCState
  locallyTCState :: Lens' TCState a -> (a -> a) -> m b -> m b

  withTCState :: (TCState -> TCState) -> m a -> m a
  withTCState = locallyTCState id

  default getTCState :: (MonadTrans t, ReadTCState n, t n ~ m) => m TCState
  getTCState = lift getTCState

  default locallyTCState
    :: (MonadTransControl t, ReadTCState n, t n ~ m)
    => Lens' TCState a -> (a -> a) -> m b -> m b
  locallyTCState l = liftThrough . locallyTCState l

instance ReadTCState m => ReadTCState (ListT m) where
  locallyTCState l = mapListT . locallyTCState l

instance ReadTCState m => ReadTCState (ChangeT m)
instance ReadTCState m => ReadTCState (ExceptT err m)
instance ReadTCState m => ReadTCState (IdentityT m)
instance ReadTCState m => ReadTCState (MaybeT m)
instance ReadTCState m => ReadTCState (ReaderT r m)
instance ReadTCState m => ReadTCState (StateT s m)
instance (Monoid w, ReadTCState m) => ReadTCState (WriterT w m)


instance Show TCState where
  show _ = "TCSt{}"

data PreScopeState = PreScopeState
  { stPreTokens             :: !HighlightingInfo
    -- ^ Highlighting info for tokens and Happy parser warnings (but
    -- not for those tokens/warnings for which highlighting exists in
    -- 'stPostSyntaxInfo').
  , stPreImports            :: !Signature  -- XX populated by scope checker
    -- ^ Imported declared identifiers.
    --   Those most not be serialized!
  , stPreImportedModules    :: !(Set TopLevelModuleName)
      -- Andreas, 2023-08-05, issue #6750, don't make this a 'HashSet'
      -- because then the order of its @toList@ is undefined,
      -- leading to undefined deserialization order.
    -- ^ The top-level modules imported by the current module.
  , stPreModuleToSource     :: !ModuleToSource   -- imports
  , stPreVisitedModules     :: !VisitedModules   -- imports
  , stPreScope              :: !ScopeInfo
    -- generated by scope checker, current file:
    -- which modules you have, public definitions, current file, maps concrete names to abstract names.
  , stPrePatternSyns        :: !A.PatternSynDefns
    -- ^ Pattern synonyms of the current file.  Serialized.
  , stPrePatternSynImports  :: !A.PatternSynDefns
    -- ^ Imported pattern synonyms.  Must not be serialized!
  , stPreGeneralizedVars    :: !(Strict.Maybe (Set QName))
    -- ^ Collected generalizable variables; used during scope checking of terms
  , stPrePragmaOptions      :: !PragmaOptions
    -- ^ Options applying to the current file. @OPTIONS@
    -- pragmas only affect this field.
  , stPreImportedBuiltins   :: !(BuiltinThings PrimFun)
  , stPreImportedDisplayForms :: !DisplayForms
    -- ^ Display forms added by someone else to imported identifiers
  , stPreImportedInstanceDefs :: !InstanceTable
  , stPreForeignCode        :: !(Map BackendName ForeignCodeStack)
    -- ^ @{-\# FOREIGN \#-}@ code that should be included in the compiled output.
    -- Does not include code for imported modules.
  , stPreFreshInteractionId :: !InteractionId
  , stPreImportedUserWarnings :: !(Map A.QName Text)
    -- ^ Imported @UserWarning@s, not to be stored in the @Interface@
  , stPreLocalUserWarnings    :: !(Map A.QName Text)
    -- ^ Locally defined @UserWarning@s, to be stored in the @Interface@
  , stPreWarningOnImport      :: !(Strict.Maybe Text)
    -- ^ Whether the current module should raise a warning when opened
  , stPreImportedPartialDefs :: !(Set QName)
    -- ^ Imported partial definitions, not to be stored in the @Interface@
  , stPreProjectConfigs :: !(Map FilePath ProjectConfig)
    -- ^ Map from directories to paths of closest enclosing .agda-lib
    --   files (or @Nothing@ if there are none).
  , stPreAgdaLibFiles   :: !(Map FilePath AgdaLibFile)
    -- ^ Contents of .agda-lib files that have already been parsed.
  , stPreImportedMetaStore :: !RemoteMetaStore
    -- ^ Used for meta-variables from other modules.
  , stPreCopiedNames       :: !(HashMap A.QName A.QName)
    -- ^ Associates a copied name (the key) to its original name (the
    -- value). Computed by the scope checker, used to compute opaque
    -- blocks.
  , stPreNameCopies        :: !(HashMap A.QName (HashSet A.QName))
    -- ^ Associates an original name (the key) to all its copies (the
    -- value). Computed by the scope checker, used to compute opaque
    -- blocks.
  }
  deriving Generic

-- | Name disambiguation for the sake of highlighting.
data DisambiguatedName = DisambiguatedName NameKind A.QName
  deriving Generic
type DisambiguatedNames = IntMap DisambiguatedName

type ConcreteNames = Map Name [C.Name]

data PostScopeState = PostScopeState
  { stPostSyntaxInfo          :: !HighlightingInfo
    -- ^ Highlighting info.
  , stPostDisambiguatedNames  :: !DisambiguatedNames
    -- ^ Disambiguation carried out by the type checker.
    --   Maps position of first name character to disambiguated @'A.QName'@
    --   for each @'A.AmbiguousQName'@ already passed by the type checker.
  , stPostOpenMetaStore       :: !LocalMetaStore
    -- ^ Used for open meta-variables.
  , stPostSolvedMetaStore     :: !LocalMetaStore
    -- ^ Used for local, instantiated meta-variables.
  , stPostInteractionPoints   :: !InteractionPoints -- scope checker first
  , stPostAwakeConstraints    :: !Constraints
  , stPostSleepingConstraints :: !Constraints
  , stPostDirty               :: !Bool -- local
    -- ^ Dirty when a constraint is added, used to prevent pointer update.
    -- Currently unused.
  , stPostOccursCheckDefs     :: !(Set QName) -- local
    -- ^ Definitions to be considered during occurs check.
    --   Initialized to the current mutual block before the check.
    --   During occurs check, we remove definitions from this set
    --   as soon we have checked them.
  , stPostSignature           :: !Signature
    -- ^ Declared identifiers of the current file.
    --   These will be serialized after successful type checking.
  , stPostModuleCheckpoints   :: !(Map ModuleName CheckpointId)
    -- ^ For each module remember the checkpoint corresponding to the orignal
    --   context of the module parameters.
  , stPostImportsDisplayForms :: !DisplayForms
    -- ^ Display forms we add for imported identifiers
  , stPostCurrentModule       ::
      !(Maybe (ModuleName, TopLevelModuleName))
    -- ^ The current module is available after it has been type
    -- checked.
  , stPostInstanceDefs        :: !TempInstanceTable
  , stPostConcreteNames       :: !ConcreteNames
    -- ^ Map keeping track of concrete names assigned to each abstract name
    --   (can be more than one name in case the first one is shadowed)
  , stPostUsedNames           :: !(Map RawName (DList RawName))
    -- ^ Map keeping track for each name root (= name w/o numeric
    -- suffixes) what names with the same root have been used during a
    -- TC computation. This information is used to build the
    -- @ShadowingNames@ map.
  , stPostShadowingNames      :: !(Map Name (DList RawName))
    -- ^ Map keeping track for each (abstract) name the list of all
    -- (raw) names that it could maybe be shadowed by.
  , stPostStatistics          :: !Statistics
    -- ^ Counters to collect various statistics about meta variables etc.
    --   Only for current file.
  , stPostTCWarnings          :: ![TCWarning]
  , stPostMutualBlocks        :: !(Map MutualId MutualBlock)
  , stPostLocalBuiltins       :: !(BuiltinThings PrimFun)
  , stPostFreshMetaId         :: !MetaId
  , stPostFreshMutualId       :: !MutualId
  , stPostFreshProblemId      :: !ProblemId
  , stPostFreshCheckpointId   :: !CheckpointId
  , stPostFreshInt            :: !Int
  , stPostFreshNameId         :: !NameId
  , stPostFreshOpaqueId       :: !OpaqueId
  , stPostAreWeCaching        :: !Bool
  , stPostPostponeInstanceSearch :: !Bool
  , stPostConsideringInstance :: !Bool
  , stPostInstantiateBlocking :: !Bool
    -- ^ Should we instantiate away blocking metas?
    --   This can produce ill-typed terms but they are often more readable. See issue #3606.
    --   Best set to True only for calls to pretty*/reify to limit unwanted reductions.
  , stPostLocalPartialDefs    :: !(Set QName)
    -- ^ Local partial definitions, to be stored in the @Interface@
  , stPostOpaqueBlocks        :: Map OpaqueId OpaqueBlock
    -- ^ Associates opaque identifiers to their actual blocks.
  , stPostOpaqueIds           :: Map QName OpaqueId
    -- ^ Associates each opaque QName to the block it was defined in.
  }
  deriving (Generic)

-- | A mutual block of names in the signature.
data MutualBlock = MutualBlock
  { mutualInfo  :: Info.MutualInfo
    -- ^ The original info of the mutual block.
  , mutualNames :: Set QName
  } deriving (Show, Eq, Generic)

instance Null MutualBlock where
  empty = MutualBlock empty empty

-- | A part of the state which is not reverted when an error is thrown
-- or the state is reset.
data PersistentTCState = PersistentTCSt
  { stDecodedModules    :: !DecodedModules
  , stPersistentTopLevelModuleNames ::
      !(BiMap RawTopLevelModuleName ModuleNameHash)
    -- ^ Module name hashes for top-level module names (and vice
    -- versa).
  , stPersistentOptions :: CommandLineOptions
  , stInteractionOutputCallback  :: InteractionOutputCallback
    -- ^ Callback function to call when there is a response
    --   to give to the interactive frontend.
    --   See the documentation of 'InteractionOutputCallback'.
  , stBenchmark         :: !Benchmark
    -- ^ Structure to track how much CPU time was spent on which Agda phase.
    --   Needs to be a strict field to avoid space leaks!
  , stAccumStatistics   :: !Statistics
    -- ^ Should be strict field.
  , stPersistLoadedFileCache :: !(Strict.Maybe LoadedFileCache)
    -- ^ Cached typechecking state from the last loaded file.
    --   Should be @Nothing@ when checking imports.
  , stPersistBackends   :: [Backend_boot TCM]
    -- ^ Current backends with their options
  }
  deriving Generic

data LoadedFileCache = LoadedFileCache
  { lfcCached  :: !CachedTypeCheckLog
  , lfcCurrent :: !CurrentTypeCheckLog
  }
  deriving Generic

-- | A log of what the type checker does and states after the action is
-- completed.  The cached version is stored first executed action first.
type CachedTypeCheckLog = [(TypeCheckAction, PostScopeState)]

-- | Like 'CachedTypeCheckLog', but storing the log for an ongoing type
-- checking of a module.  Stored in reverse order (last performed action
-- first).
type CurrentTypeCheckLog = [(TypeCheckAction, PostScopeState)]

-- | A complete log for a module will look like this:
--
--   * 'Pragmas'
--
--   * 'EnterSection', entering the main module.
--
--   * 'Decl'/'EnterSection'/'LeaveSection', for declarations and nested
--     modules
--
--   * 'LeaveSection', leaving the main module.
data TypeCheckAction
  = EnterSection !Erased !ModuleName !A.Telescope
  | LeaveSection !ModuleName
  | Decl !A.Declaration
    -- ^ Never a Section or ScopeDecl
  | Pragmas !PragmaOptions
  deriving (Generic)

-- | Empty persistent state.

initPersistentState :: PersistentTCState
initPersistentState = PersistentTCSt
  { stPersistentOptions         = defaultOptions
  , stPersistentTopLevelModuleNames = empty
  , stDecodedModules            = Map.empty
  , stInteractionOutputCallback = defaultInteractionOutputCallback
  , stBenchmark                 = empty
  , stAccumStatistics           = Map.empty
  , stPersistLoadedFileCache    = empty
  , stPersistBackends           = []
  }

-- | An initial 'MetaId'.

initialMetaId :: MetaId
initialMetaId = MetaId
  { metaId     = 0
  , metaModule = noModuleNameHash
  }

-- | Empty state of type checker.

initPreScopeState :: PreScopeState
initPreScopeState = PreScopeState
  { stPreTokens               = mempty
  , stPreImports              = emptySignature
  , stPreImportedModules      = empty
  , stPreModuleToSource       = Map.empty
  , stPreVisitedModules       = Map.empty
  , stPreScope                = emptyScopeInfo
  , stPrePatternSyns          = Map.empty
  , stPrePatternSynImports    = Map.empty
  , stPreGeneralizedVars      = mempty
  , stPrePragmaOptions        = defaultInteractionOptions
  , stPreImportedBuiltins     = Map.empty
  , stPreImportedDisplayForms = HMap.empty
  , stPreImportedInstanceDefs = Map.empty
  , stPreForeignCode          = Map.empty
  , stPreFreshInteractionId   = 0
  , stPreImportedUserWarnings = Map.empty
  , stPreLocalUserWarnings    = Map.empty
  , stPreWarningOnImport      = empty
  , stPreImportedPartialDefs  = Set.empty
  , stPreProjectConfigs       = Map.empty
  , stPreAgdaLibFiles         = Map.empty
  , stPreImportedMetaStore    = HMap.empty
  , stPreCopiedNames          = HMap.empty
  , stPreNameCopies           = HMap.empty
  }

initPostScopeState :: PostScopeState
initPostScopeState = PostScopeState
  { stPostSyntaxInfo           = mempty
  , stPostDisambiguatedNames   = IntMap.empty
  , stPostOpenMetaStore        = Map.empty
  , stPostSolvedMetaStore      = Map.empty
  , stPostInteractionPoints    = empty
  , stPostAwakeConstraints     = []
  , stPostSleepingConstraints  = []
  , stPostDirty                = False
  , stPostOccursCheckDefs      = Set.empty
  , stPostSignature            = emptySignature
  , stPostModuleCheckpoints    = Map.empty
  , stPostImportsDisplayForms  = HMap.empty
  , stPostCurrentModule        = empty
  , stPostInstanceDefs         = (Map.empty , Set.empty)
  , stPostConcreteNames        = Map.empty
  , stPostUsedNames            = Map.empty
  , stPostShadowingNames       = Map.empty
  , stPostStatistics           = Map.empty
  , stPostTCWarnings           = []
  , stPostMutualBlocks         = Map.empty
  , stPostLocalBuiltins        = Map.empty
  , stPostFreshMetaId          = initialMetaId
  , stPostFreshMutualId        = 0
  , stPostFreshProblemId       = 1
  , stPostFreshCheckpointId    = 1
  , stPostFreshInt             = 0
  , stPostFreshNameId          = NameId 0 noModuleNameHash
  , stPostFreshOpaqueId        = OpaqueId 0 noModuleNameHash
  , stPostAreWeCaching         = False
  , stPostPostponeInstanceSearch = False
  , stPostConsideringInstance  = False
  , stPostInstantiateBlocking  = False
  , stPostLocalPartialDefs     = Set.empty
  , stPostOpaqueBlocks         = Map.empty
  , stPostOpaqueIds            = Map.empty
  }

initState :: TCState
initState = TCSt
  { stPreScopeState   = initPreScopeState
  , stPostScopeState  = initPostScopeState
  , stPersistentState = initPersistentState
  }

-- * st-prefixed lenses
------------------------------------------------------------------------

stTokens :: Lens' TCState HighlightingInfo
stTokens f s =
  f (stPreTokens (stPreScopeState s)) <&>
  \x -> s {stPreScopeState = (stPreScopeState s) {stPreTokens = x}}

stImports :: Lens' TCState Signature
stImports f s =
  f (stPreImports (stPreScopeState s)) <&>
  \x -> s {stPreScopeState = (stPreScopeState s) {stPreImports = x}}

stImportedModules ::
  Lens' TCState (Set TopLevelModuleName)
stImportedModules f s =
  f (stPreImportedModules (stPreScopeState s)) <&>
  \x -> s {stPreScopeState = (stPreScopeState s) {stPreImportedModules = x}}

stModuleToSource :: Lens' TCState ModuleToSource
stModuleToSource f s =
  f (stPreModuleToSource (stPreScopeState s)) <&>
  \x -> s {stPreScopeState = (stPreScopeState s) {stPreModuleToSource = x}}

stVisitedModules :: Lens' TCState VisitedModules
stVisitedModules f s =
  f (stPreVisitedModules (stPreScopeState s)) <&>
  \x -> s {stPreScopeState = (stPreScopeState s) {stPreVisitedModules = x}}

stScope :: Lens' TCState ScopeInfo
stScope f s =
  f (stPreScope (stPreScopeState s)) <&>
  \x -> s {stPreScopeState = (stPreScopeState s) {stPreScope = x}}

stPatternSyns :: Lens' TCState A.PatternSynDefns
stPatternSyns f s =
  f (stPrePatternSyns (stPreScopeState s)) <&>
  \x -> s {stPreScopeState = (stPreScopeState s) {stPrePatternSyns = x}}

stPatternSynImports :: Lens' TCState A.PatternSynDefns
stPatternSynImports f s =
  f (stPrePatternSynImports (stPreScopeState s)) <&>
  \x -> s {stPreScopeState = (stPreScopeState s) {stPrePatternSynImports = x}}

stGeneralizedVars :: Lens' TCState (Maybe (Set QName))
stGeneralizedVars f s =
  f (Strict.toLazy $ stPreGeneralizedVars (stPreScopeState s)) <&>
  \x -> s {stPreScopeState = (stPreScopeState s) {stPreGeneralizedVars = Strict.toStrict x}}

stPragmaOptions :: Lens' TCState PragmaOptions
stPragmaOptions f s =
  f (stPrePragmaOptions (stPreScopeState s)) <&>
  \x -> s {stPreScopeState = (stPreScopeState s) {stPrePragmaOptions = x}}

stImportedBuiltins :: Lens' TCState (BuiltinThings PrimFun)
stImportedBuiltins f s =
  f (stPreImportedBuiltins (stPreScopeState s)) <&>
  \x -> s {stPreScopeState = (stPreScopeState s) {stPreImportedBuiltins = x}}

stForeignCode :: Lens' TCState (Map BackendName ForeignCodeStack)
stForeignCode f s =
  f (stPreForeignCode (stPreScopeState s)) <&>
  \x -> s {stPreScopeState = (stPreScopeState s) {stPreForeignCode = x}}

stFreshInteractionId :: Lens' TCState InteractionId
stFreshInteractionId f s =
  f (stPreFreshInteractionId (stPreScopeState s)) <&>
  \x -> s {stPreScopeState = (stPreScopeState s) {stPreFreshInteractionId = x}}

stImportedUserWarnings :: Lens' TCState (Map A.QName Text)
stImportedUserWarnings f s =
  f (stPreImportedUserWarnings (stPreScopeState s)) <&>
  \ x -> s {stPreScopeState = (stPreScopeState s) {stPreImportedUserWarnings = x}}

stLocalUserWarnings :: Lens' TCState (Map A.QName Text)
stLocalUserWarnings f s =
  f (stPreLocalUserWarnings (stPreScopeState s)) <&>
  \ x -> s {stPreScopeState = (stPreScopeState s) {stPreLocalUserWarnings = x}}

getUserWarnings :: ReadTCState m => m (Map A.QName Text)
getUserWarnings = do
  iuw <- useR stImportedUserWarnings
  luw <- useR stLocalUserWarnings
  return $ iuw `Map.union` luw

stWarningOnImport :: Lens' TCState (Maybe Text)
stWarningOnImport f s =
  f (Strict.toLazy $ stPreWarningOnImport (stPreScopeState s)) <&>
  \ x -> s {stPreScopeState = (stPreScopeState s) {stPreWarningOnImport = Strict.toStrict x}}

stImportedPartialDefs :: Lens' TCState (Set QName)
stImportedPartialDefs f s =
  f (stPreImportedPartialDefs (stPreScopeState s)) <&>
  \ x -> s {stPreScopeState = (stPreScopeState s) {stPreImportedPartialDefs = x}}

stLocalPartialDefs :: Lens' TCState (Set QName)
stLocalPartialDefs f s =
  f (stPostLocalPartialDefs (stPostScopeState s)) <&>
  \ x -> s {stPostScopeState = (stPostScopeState s) {stPostLocalPartialDefs = x}}

getPartialDefs :: ReadTCState m => m (Set QName)
getPartialDefs = do
  ipd <- useR stImportedPartialDefs
  lpd <- useR stLocalPartialDefs
  return $ ipd `Set.union` lpd

stLoadedFileCache :: Lens' TCState (Maybe LoadedFileCache)
stLoadedFileCache f s =
  f (Strict.toLazy $ stPersistLoadedFileCache (stPersistentState s)) <&>
  \x -> s {stPersistentState = (stPersistentState s) {stPersistLoadedFileCache = Strict.toStrict x}}

stBackends :: Lens' TCState [Backend_boot TCM]
stBackends f s =
  f (stPersistBackends (stPersistentState s)) <&>
  \x -> s {stPersistentState = (stPersistentState s) {stPersistBackends = x}}

stProjectConfigs :: Lens' TCState (Map FilePath ProjectConfig)
stProjectConfigs f s =
  f (stPreProjectConfigs (stPreScopeState s)) <&>
  \ x -> s {stPreScopeState = (stPreScopeState s) {stPreProjectConfigs = x}}

stAgdaLibFiles :: Lens' TCState (Map FilePath AgdaLibFile)
stAgdaLibFiles f s =
  f (stPreAgdaLibFiles (stPreScopeState s)) <&>
  \ x -> s {stPreScopeState = (stPreScopeState s) {stPreAgdaLibFiles = x}}

stTopLevelModuleNames ::
  Lens' TCState (BiMap RawTopLevelModuleName ModuleNameHash)
stTopLevelModuleNames f s =
  f (stPersistentTopLevelModuleNames (stPersistentState s)) <&>
  \ x -> s {stPersistentState =
              (stPersistentState s) {stPersistentTopLevelModuleNames = x}}

stImportedMetaStore :: Lens' TCState RemoteMetaStore
stImportedMetaStore f s =
  f (stPreImportedMetaStore (stPreScopeState s)) <&>
  \x -> s {stPreScopeState = (stPreScopeState s) {stPreImportedMetaStore = x}}

stCopiedNames :: Lens' TCState (HashMap QName QName)
stCopiedNames f s =
  f (stPreCopiedNames (stPreScopeState s)) <&>
  \x -> s {stPreScopeState = (stPreScopeState s) {stPreCopiedNames = x}}

stNameCopies :: Lens' TCState (HashMap QName (HashSet QName))
stNameCopies f s =
  f (stPreNameCopies (stPreScopeState s)) <&>
  \x -> s {stPreScopeState = (stPreScopeState s) {stPreNameCopies = x}}

stFreshNameId :: Lens' TCState NameId
stFreshNameId f s =
  f (stPostFreshNameId (stPostScopeState s)) <&>
  \x -> s {stPostScopeState = (stPostScopeState s) {stPostFreshNameId = x}}

stFreshOpaqueId :: Lens' TCState OpaqueId
stFreshOpaqueId f s =
  f (stPostFreshOpaqueId (stPostScopeState s)) <&>
  \x -> s {stPostScopeState = (stPostScopeState s) {stPostFreshOpaqueId = x}}

stOpaqueBlocks :: Lens' TCState (Map OpaqueId OpaqueBlock)
stOpaqueBlocks f s =
  f (stPostOpaqueBlocks (stPostScopeState s)) <&>
  \x -> s {stPostScopeState = (stPostScopeState s) {stPostOpaqueBlocks = x}}

stOpaqueIds :: Lens' TCState (Map QName OpaqueId)
stOpaqueIds f s =
  f (stPostOpaqueIds (stPostScopeState s)) <&>
  \x -> s {stPostScopeState = (stPostScopeState s) {stPostOpaqueIds = x}}

stSyntaxInfo :: Lens' TCState HighlightingInfo
stSyntaxInfo f s =
  f (stPostSyntaxInfo (stPostScopeState s)) <&>
  \x -> s {stPostScopeState = (stPostScopeState s) {stPostSyntaxInfo = x}}

stDisambiguatedNames :: Lens' TCState DisambiguatedNames
stDisambiguatedNames f s =
  f (stPostDisambiguatedNames (stPostScopeState s)) <&>
  \x -> s {stPostScopeState = (stPostScopeState s) {stPostDisambiguatedNames = x}}

stOpenMetaStore :: Lens' TCState LocalMetaStore
stOpenMetaStore f s =
  f (stPostOpenMetaStore (stPostScopeState s)) <&>
  \x -> s {stPostScopeState = (stPostScopeState s) {stPostOpenMetaStore = x}}

stSolvedMetaStore :: Lens' TCState LocalMetaStore
stSolvedMetaStore f s =
  f (stPostSolvedMetaStore (stPostScopeState s)) <&>
  \x -> s {stPostScopeState = (stPostScopeState s) {stPostSolvedMetaStore = x}}

stInteractionPoints :: Lens' TCState InteractionPoints
stInteractionPoints f s =
  f (stPostInteractionPoints (stPostScopeState s)) <&>
  \x -> s {stPostScopeState = (stPostScopeState s) {stPostInteractionPoints = x}}

stAwakeConstraints :: Lens' TCState Constraints
stAwakeConstraints f s =
  f (stPostAwakeConstraints (stPostScopeState s)) <&>
  \x -> s {stPostScopeState = (stPostScopeState s) {stPostAwakeConstraints = x}}

stSleepingConstraints :: Lens' TCState Constraints
stSleepingConstraints f s =
  f (stPostSleepingConstraints (stPostScopeState s)) <&>
  \x -> s {stPostScopeState = (stPostScopeState s) {stPostSleepingConstraints = x}}

stDirty :: Lens' TCState Bool
stDirty f s =
  f (stPostDirty (stPostScopeState s)) <&>
  \x -> s {stPostScopeState = (stPostScopeState s) {stPostDirty = x}}

stOccursCheckDefs :: Lens' TCState (Set QName)
stOccursCheckDefs f s =
  f (stPostOccursCheckDefs (stPostScopeState s)) <&>
  \x -> s {stPostScopeState = (stPostScopeState s) {stPostOccursCheckDefs = x}}

stSignature :: Lens' TCState Signature
stSignature f s =
  f (stPostSignature (stPostScopeState s)) <&>
  \x -> s {stPostScopeState = (stPostScopeState s) {stPostSignature = x}}

stModuleCheckpoints :: Lens' TCState (Map ModuleName CheckpointId)
stModuleCheckpoints f s =
  f (stPostModuleCheckpoints (stPostScopeState s)) <&>
  \x -> s {stPostScopeState = (stPostScopeState s) {stPostModuleCheckpoints = x}}

stImportsDisplayForms :: Lens' TCState DisplayForms
stImportsDisplayForms f s =
  f (stPostImportsDisplayForms (stPostScopeState s)) <&>
  \x -> s {stPostScopeState = (stPostScopeState s) {stPostImportsDisplayForms = x}}

stImportedDisplayForms :: Lens' TCState DisplayForms
stImportedDisplayForms f s =
  f (stPreImportedDisplayForms (stPreScopeState s)) <&>
  \x -> s {stPreScopeState = (stPreScopeState s) {stPreImportedDisplayForms = x}}

-- | Note that the lens is \"strict\".

stCurrentModule ::
  Lens' TCState (Maybe (ModuleName, TopLevelModuleName))
stCurrentModule f s =
  f (stPostCurrentModule (stPostScopeState s)) <&>
  \x -> s {stPostScopeState =
             (stPostScopeState s)
               {stPostCurrentModule = case x of
                  Nothing         -> Nothing
                  Just (!m, !top) -> Just (m, top)}}

stImportedInstanceDefs :: Lens' TCState InstanceTable
stImportedInstanceDefs f s =
  f (stPreImportedInstanceDefs (stPreScopeState s)) <&>
  \x -> s {stPreScopeState = (stPreScopeState s) {stPreImportedInstanceDefs = x}}

stInstanceDefs :: Lens' TCState TempInstanceTable
stInstanceDefs f s =
  f (stPostInstanceDefs (stPostScopeState s)) <&>
  \x -> s {stPostScopeState = (stPostScopeState s) {stPostInstanceDefs = x}}

stConcreteNames :: Lens' TCState ConcreteNames
stConcreteNames f s =
  f (stPostConcreteNames (stPostScopeState s)) <&>
  \x -> s {stPostScopeState = (stPostScopeState s) {stPostConcreteNames = x}}

stUsedNames :: Lens' TCState (Map RawName (DList RawName))
stUsedNames f s =
  f (stPostUsedNames (stPostScopeState s)) <&>
  \x -> s {stPostScopeState = (stPostScopeState s) {stPostUsedNames = x}}

stShadowingNames :: Lens' TCState (Map Name (DList RawName))
stShadowingNames f s =
  f (stPostShadowingNames (stPostScopeState s)) <&>
  \x -> s {stPostScopeState = (stPostScopeState s) {stPostShadowingNames = x}}

stStatistics :: Lens' TCState Statistics
stStatistics f s =
  f (stPostStatistics (stPostScopeState s)) <&>
  \x -> s {stPostScopeState = (stPostScopeState s) {stPostStatistics = x}}

stTCWarnings :: Lens' TCState [TCWarning]
stTCWarnings f s =
  f (stPostTCWarnings (stPostScopeState s)) <&>
  \x -> s {stPostScopeState = (stPostScopeState s) {stPostTCWarnings = x}}

stMutualBlocks :: Lens' TCState (Map MutualId MutualBlock)
stMutualBlocks f s =
  f (stPostMutualBlocks (stPostScopeState s)) <&>
  \x -> s {stPostScopeState = (stPostScopeState s) {stPostMutualBlocks = x}}

stLocalBuiltins :: Lens' TCState (BuiltinThings PrimFun)
stLocalBuiltins f s =
  f (stPostLocalBuiltins (stPostScopeState s)) <&>
  \x -> s {stPostScopeState = (stPostScopeState s) {stPostLocalBuiltins = x}}

stFreshMetaId :: Lens' TCState MetaId
stFreshMetaId f s =
  f (stPostFreshMetaId (stPostScopeState s)) <&>
  \x -> s {stPostScopeState = (stPostScopeState s) {stPostFreshMetaId = x}}

stFreshMutualId :: Lens' TCState MutualId
stFreshMutualId f s =
  f (stPostFreshMutualId (stPostScopeState s)) <&>
  \x -> s {stPostScopeState = (stPostScopeState s) {stPostFreshMutualId = x}}

stFreshProblemId :: Lens' TCState ProblemId
stFreshProblemId f s =
  f (stPostFreshProblemId (stPostScopeState s)) <&>
  \x -> s {stPostScopeState = (stPostScopeState s) {stPostFreshProblemId = x}}

stFreshCheckpointId :: Lens' TCState CheckpointId
stFreshCheckpointId f s =
  f (stPostFreshCheckpointId (stPostScopeState s)) <&>
  \x -> s {stPostScopeState = (stPostScopeState s) {stPostFreshCheckpointId = x}}

stFreshInt :: Lens' TCState Int
stFreshInt f s =
  f (stPostFreshInt (stPostScopeState s)) <&>
  \x -> s {stPostScopeState = (stPostScopeState s) {stPostFreshInt = x}}

-- use @areWeCaching@ from the Caching module instead.
stAreWeCaching :: Lens' TCState Bool
stAreWeCaching f s =
  f (stPostAreWeCaching (stPostScopeState s)) <&>
  \x -> s {stPostScopeState = (stPostScopeState s) {stPostAreWeCaching = x}}

stPostponeInstanceSearch :: Lens' TCState Bool
stPostponeInstanceSearch f s =
  f (stPostPostponeInstanceSearch (stPostScopeState s)) <&>
  \x -> s {stPostScopeState = (stPostScopeState s) {stPostPostponeInstanceSearch = x}}

stConsideringInstance :: Lens' TCState Bool
stConsideringInstance f s =
  f (stPostConsideringInstance (stPostScopeState s)) <&>
  \x -> s {stPostScopeState = (stPostScopeState s) {stPostConsideringInstance = x}}

stInstantiateBlocking :: Lens' TCState Bool
stInstantiateBlocking f s =
  f (stPostInstantiateBlocking (stPostScopeState s)) <&>
  \x -> s {stPostScopeState = (stPostScopeState s) {stPostInstantiateBlocking = x}}

stBuiltinThings :: TCState -> BuiltinThings PrimFun
stBuiltinThings s = Map.unionWith unionBuiltin (s ^. stLocalBuiltins) (s ^. stImportedBuiltins)

-- | Union two 'Builtin's.  Only defined for 'BuiltinRewriteRelations'.
unionBuiltin :: Builtin a -> Builtin a -> Builtin a
unionBuiltin = curry $ \case
  (BuiltinRewriteRelations xs, BuiltinRewriteRelations ys) -> BuiltinRewriteRelations $ xs <> ys
  _ -> __IMPOSSIBLE__


-- * Fresh things
------------------------------------------------------------------------

class Enum i => HasFresh i where
    freshLens :: Lens' TCState i
    nextFresh' :: i -> i
    nextFresh' = succ

{-# INLINE nextFresh #-}
nextFresh :: HasFresh i => TCState -> (i, TCState)
nextFresh s =
  let !c = s ^. freshLens
      !next = set freshLens (nextFresh' c) s
  in (c, next)

class Monad m => MonadFresh i m where
  fresh :: m i

  default fresh :: (MonadTrans t, MonadFresh i n, t n ~ m) => m i
  fresh = lift fresh

instance MonadFresh i m => MonadFresh i (ReaderT r m)
instance MonadFresh i m => MonadFresh i (StateT s m)
instance MonadFresh i m => MonadFresh i (ListT m)
instance MonadFresh i m => MonadFresh i (IdentityT m)

instance HasFresh i => MonadFresh i TCM where
  fresh = do
        !s <- getTC
        let (!c , !s') = nextFresh s
        putTC s'
        return c
  {-# INLINE fresh #-}

instance HasFresh MetaId where
  freshLens = stFreshMetaId

instance HasFresh MutualId where
  freshLens = stFreshMutualId

instance HasFresh InteractionId where
  freshLens = stFreshInteractionId

instance HasFresh NameId where
  freshLens = stFreshNameId
  -- nextFresh increments the current fresh name by 2 so @NameId@s used
  -- before caching starts do not overlap with the ones used after.
  nextFresh' = succ . succ

instance HasFresh OpaqueId where
  freshLens = stFreshOpaqueId

instance HasFresh Int where
  freshLens = stFreshInt

instance HasFresh ProblemId where
  freshLens = stFreshProblemId

newtype CheckpointId = CheckpointId Int
  deriving (Eq, Ord, Enum, Real, Integral, Num, NFData)

instance Show CheckpointId where
  show (CheckpointId n) = show n

instance Pretty CheckpointId where
  pretty (CheckpointId n) = pretty n

instance HasFresh CheckpointId where
  freshLens = stFreshCheckpointId

freshName :: MonadFresh NameId m => Range -> String -> m Name
freshName r s = do
  i <- fresh
  return $ mkName r i s

freshNoName :: MonadFresh NameId m => Range -> m Name
freshNoName r =
    do  i <- fresh
        return $ makeName i (C.NoName noRange i) r noFixity' False

freshNoName_ :: MonadFresh NameId m => m Name
freshNoName_ = freshNoName noRange

freshRecordName :: MonadFresh NameId m => m Name
freshRecordName = do
  i <- fresh
  return $ makeName i (C.setNotInScope $ C.simpleName "r") noRange noFixity' True

-- | Create a fresh name from @a@.
class FreshName a where
  freshName_ :: MonadFresh NameId m => a -> m Name

instance FreshName (Range, String) where
  freshName_ = uncurry freshName

instance FreshName String where
  freshName_ = freshName noRange

instance FreshName Range where
  freshName_ = freshNoName

instance FreshName () where
  freshName_ () = freshNoName_

---------------------------------------------------------------------------
-- ** Managing file names
---------------------------------------------------------------------------

-- | Maps top-level module names to the corresponding source file
-- names.

type ModuleToSource = Map TopLevelModuleName AbsolutePath

---------------------------------------------------------------------------
-- ** Associating concrete names to an abstract name
---------------------------------------------------------------------------

-- | A monad that has read and write access to the stConcreteNames
--   part of the TCState. Basically, this is a synonym for `MonadState
--   ConcreteNames m` (which cannot be used directly because of the
--   limitations of Haskell's typeclass system).
class Monad m => MonadStConcreteNames m where
  runStConcreteNames :: StateT ConcreteNames m a -> m a

  useConcreteNames :: m ConcreteNames
  useConcreteNames = runStConcreteNames get

  modifyConcreteNames :: (ConcreteNames -> ConcreteNames) -> m ()
  modifyConcreteNames = runStConcreteNames . modify

instance MonadStConcreteNames TCM where
  runStConcreteNames m = stateTCLensM stConcreteNames $ runStateT m

instance MonadStConcreteNames m => MonadStConcreteNames (IdentityT m) where
  runStConcreteNames m = IdentityT $ runStConcreteNames $ StateT $ runIdentityT . runStateT m

instance MonadStConcreteNames m => MonadStConcreteNames (ReaderT r m) where
  runStConcreteNames m = ReaderT $ runStConcreteNames . StateT . flip (runReaderT . runStateT m)

instance MonadStConcreteNames m => MonadStConcreteNames (StateT s m) where
  runStConcreteNames m = StateT $ \s -> runStConcreteNames $ StateT $ \ns -> do
    ((x,ns'),s') <- runStateT (runStateT m ns) s
    return ((x,s'),ns')

---------------------------------------------------------------------------
-- ** Interface
---------------------------------------------------------------------------


-- | Distinguishes between type-checked and scope-checked interfaces
--   when stored in the map of `VisitedModules`.
data ModuleCheckMode
  = ModuleScopeChecked
  | ModuleTypeChecked
  deriving (Eq, Ord, Bounded, Enum, Show, Generic)


data ModuleInfo = ModuleInfo
  { miInterface  :: Interface
  , miWarnings   :: [TCWarning]
    -- ^ Warnings were encountered when the module was type checked.
    --   These might include warnings not stored in the interface itself,
    --   specifically unsolved interaction metas.
    --   See "Agda.Interaction.Imports"
  , miPrimitive  :: Bool
    -- ^ 'True' if the module is a primitive module, which should always
    -- be importable.
  , miMode       :: ModuleCheckMode
    -- ^ The `ModuleCheckMode` used to create the `Interface`
  }
  deriving Generic

type VisitedModules = Map TopLevelModuleName ModuleInfo
type DecodedModules = Map TopLevelModuleName ModuleInfo

data ForeignCode = ForeignCode Range String
  deriving (Show, Generic)

-- | Foreign code fragments are stored in reversed order to support efficient appending:
--   head points to the latest pragma in module.
newtype ForeignCodeStack = ForeignCodeStack
  { getForeignCodeStack :: [ForeignCode]
  } deriving (Show, Generic, NFData)

data Interface = Interface
  { iSourceHash      :: Hash
    -- ^ Hash of the source code.
  , iSource          :: TL.Text
    -- ^ The source code. The source code is stored so that the HTML
    -- and LaTeX backends can generate their output without having to
    -- re-read the (possibly out of date) source code.
  , iFileType        :: FileType
    -- ^ Source file type, determined from the file extension
  , iImportedModules :: [(TopLevelModuleName, Hash)]
    -- ^ Imported modules and their hashes.
  , iModuleName      :: ModuleName
    -- ^ Module name of this interface.
  , iTopLevelModuleName :: TopLevelModuleName
    -- ^ The module's top-level module name.
  , iScope           :: Map ModuleName Scope
    -- ^ Scope defined by this module.
    --
    --   Andreas, AIM XX: Too avoid duplicate serialization, this field is
    --   not serialized, so if you deserialize an interface, @iScope@
    --   will be empty.
    --   But 'constructIScope' constructs 'iScope' from 'iInsideScope'.
  , iInsideScope     :: ScopeInfo
    -- ^ Scope after we loaded this interface.
    --   Used in 'Agda.Interaction.BasicOps.AtTopLevel'
    --   and     'Agda.Interaction.CommandLine.interactionLoop'.
  , iSignature       :: Signature
  , iMetaBindings    :: RemoteMetaStore
    -- ^ Instantiations for meta-variables that come from this module.
  , iDisplayForms    :: DisplayForms
    -- ^ Display forms added for imported identifiers.
  , iUserWarnings    :: Map A.QName Text
    -- ^ User warnings for imported identifiers
  , iImportWarning   :: Maybe Text
    -- ^ Whether this module should raise a warning when imported
  , iBuiltin         :: BuiltinThings (PrimitiveId, QName)
  , iForeignCode     :: Map BackendName ForeignCodeStack
  , iHighlighting    :: HighlightingInfo
  , iDefaultPragmaOptions :: [OptionsPragma]
    -- ^ Pragma options set in library files.
  , iFilePragmaOptions    :: [OptionsPragma]
    -- ^ Pragma options set in the file.
  , iOptionsUsed     :: PragmaOptions
    -- ^ Options/features used when checking the file (can be different
    --   from options set directly in the file).
  , iPatternSyns     :: A.PatternSynDefns
  , iWarnings        :: [TCWarning]
  , iPartialDefs     :: Set QName
  , iOpaqueBlocks    :: Map OpaqueId OpaqueBlock
  , iOpaqueNames     :: Map QName OpaqueId
  }
  deriving (Show, Generic)

instance Pretty Interface where
  pretty (Interface
            sourceH source fileT importedM moduleN topModN scope insideS
            signature metas display userwarn importwarn builtin
            foreignCode highlighting libPragmaO filePragmaO oUsed
            patternS warnings partialdefs oblocks onames) =

    hang "Interface" 2 $ vcat
      [ "source hash:"         <+> (pretty . show) sourceH
      , "source:"              $$  nest 2 (text $ TL.unpack source)
      , "file type:"           <+> (pretty . show) fileT
      , "imported modules:"    <+> (pretty . show) importedM
      , "module name:"         <+> pretty moduleN
      , "top-level module name:" <+> pretty topModN
      , "scope:"               <+> (pretty . show) scope
      , "inside scope:"        <+> (pretty . show) insideS
      , "signature:"           <+> (pretty . show) signature
      , "meta-variables:"      <+> (pretty . show) metas
      , "display:"             <+> (pretty . show) display
      , "user warnings:"       <+> (pretty . show) userwarn
      , "import warning:"      <+> (pretty . show) importwarn
      , "builtin:"             <+> (pretty . show) builtin
      , "Foreign code:"        <+> (pretty . show) foreignCode
      , "highlighting:"        <+> (pretty . show) highlighting
      , "library pragma options:" <+> (pretty . show) libPragmaO
      , "file pragma options:" <+> (pretty . show) filePragmaO
      , "options used:"        <+> (pretty . show) oUsed
      , "pattern syns:"        <+> (pretty . show) patternS
      , "warnings:"            <+> (pretty . show) warnings
      , "partial definitions:" <+> (pretty . show) partialdefs
      , "opaque blocks:"       <+> pretty oblocks
      , "opaque names"         <+> pretty onames
      ]

-- | Combines the source hash and the (full) hashes of the imported modules.
iFullHash :: Interface -> Hash
iFullHash i = combineHashes $ iSourceHash i : List.map snd (iImportedModules i)

-- | A lens for the 'iSignature' field of the 'Interface' type.

intSignature :: Lens' Interface Signature
intSignature f i = f (iSignature i) <&> \s -> i { iSignature = s }

---------------------------------------------------------------------------
-- ** Closure
---------------------------------------------------------------------------

data Closure a = Closure
  { clSignature        :: Signature
  , clEnv              :: TCEnv
  , clScope            :: ScopeInfo
  , clModuleCheckpoints :: Map ModuleName CheckpointId
  , clValue            :: a
  }
    deriving (Functor, Foldable, Generic)

instance Show a => Show (Closure a) where
  show cl = "Closure { clValue = " ++ show (clValue cl) ++ " }"

instance HasRange a => HasRange (Closure a) where
  getRange = getRange . clValue

class LensClosure b a | b -> a where
  lensClosure :: Lens' b (Closure a)

instance LensClosure (Closure a) a where
  lensClosure = id

instance LensTCEnv (Closure a) where
  lensTCEnv f cl = (f $! clEnv cl) <&> \ env -> cl { clEnv = env }

{-# SPECIALIZE buildClosure :: a -> TCM (Closure a)  #-}
buildClosure :: (MonadTCEnv m, ReadTCState m) => a -> m (Closure a)
buildClosure x = do
    env   <- askTC
    sig   <- useR stSignature
    scope <- useR stScope
    cps   <- useR stModuleCheckpoints
    return $ Closure sig env scope cps x

---------------------------------------------------------------------------
-- ** Constraints
---------------------------------------------------------------------------

type Constraints = [ProblemConstraint]

data ProblemConstraint = PConstr
  { constraintProblems  :: Set ProblemId
  , constraintUnblocker :: Blocker
  , theConstraint       :: Closure Constraint
  }
  deriving (Show, Generic)

instance HasRange ProblemConstraint where
  getRange = getRange . theConstraint

-- | Why are we performing a modality check?
data WhyCheckModality
  = ConstructorType
  -- ^ Because --without-K is enabled, so the types of data constructors
  -- must be usable at the context's modality.
  | IndexedClause
  -- ^ Because --without-K is enabled, so the result type of clauses
  -- must be usable at the context's modality.
  | IndexedClauseArg Name Name
  -- ^ Because --without-K is enabled, so any argument (second name)
  -- which mentions a dotted argument (first name) must have a type
  -- which is usable at the context's modality.
  | GeneratedClause
  -- ^ Because we double-check the --cubical-compatible clauses. This is
  -- an internal error!
  deriving (Show, Generic)

data Constraint
  = ValueCmp Comparison CompareAs Term Term
  | ValueCmpOnFace Comparison Term Type Term Term
  | ElimCmp [Polarity] [IsForced] Type Term [Elim] [Elim]
  | SortCmp Comparison Sort Sort
  | LevelCmp Comparison Level Level
--  | ShortCut MetaId Term Type
--    -- ^ A delayed instantiation.  Replaces @ValueCmp@ in 'postponeTypeCheckingProblem'.
  | HasBiggerSort Sort
  | HasPTSRule (Dom Type) (Abs Sort)
  | CheckDataSort QName Sort
    -- ^ Check that the sort 'Sort' of data type 'QName' admits data/record types.
    -- E.g., sorts @IUniv@, @SizeUniv@ etc. do not admit such constructions.
    -- See 'Agda.TypeChecking.Rules.Data.checkDataSort'.
  | CheckMetaInst MetaId
  | CheckType Type
  | UnBlock MetaId
    -- ^ Meta created for a term blocked by a postponed type checking problem or unsolved
    --   constraints. The 'MetaInstantiation' for the meta (when unsolved) is either 'BlockedConst'
    --   or 'PostponedTypeCheckingProblem'.
  | IsEmpty Range Type
    -- ^ The range is the one of the absurd pattern.
  | CheckSizeLtSat Term
    -- ^ Check that the 'Term' is either not a SIZELT or a non-empty SIZELT.
  | FindInstance MetaId (Maybe [Candidate])
    -- ^ the first argument is the instance argument and the second one is the list of candidates
    --   (or Nothing if we haven’t determined the list of candidates yet)
  | ResolveInstanceHead QName
    -- ^ Resolve the head symbol of the type that the given instance targets
  | CheckFunDef A.DefInfo QName [A.Clause] TCErr
    -- ^ Last argument is the error causing us to postpone.
  | UnquoteTactic Term Term Type   -- ^ First argument is computation and the others are hole and goal type
  | CheckLockedVars Term Type (Arg Term) Type     -- ^ @CheckLockedVars t ty lk lk_ty@ with @t : ty@, @lk : lk_ty@ and @t lk@ well-typed.
  | UsableAtModality WhyCheckModality (Maybe Sort) Modality Term
    -- ^ Is the term usable at the given modality?
    -- This check should run if the @Sort@ is @Nothing@ or @isFibrant@.
  deriving (Show, Generic)

instance HasRange Constraint where
  getRange (IsEmpty r t) = r
  getRange _ = noRange
{- no Range instances for Term, Type, Elm, Tele, Sort, Level, MetaId
  getRange (ValueCmp cmp a u v) = getRange (a,u,v)
  getRange (ElimCmp pol a v es es') = getRange (a,v,es,es')
  getRange (TelCmp a b cmp tel tel') = getRange (a,b,tel,tel')
  getRange (SortCmp cmp s s') = getRange (s,s')
  getRange (LevelCmp cmp l l') = getRange (l,l')
  getRange (UnBlock x) = getRange x
  getRange (FindInstance x cands) = getRange x
-}

instance Free Constraint where
  freeVars' c =
    case c of
      ValueCmp _ t u v      -> freeVars' (t, (u, v))
      ValueCmpOnFace _ p t u v -> freeVars' (p, (t, (u, v)))
      ElimCmp _ _ t u es es'  -> freeVars' ((t, u), (es, es'))
      SortCmp _ s s'        -> freeVars' (s, s')
      LevelCmp _ l l'       -> freeVars' (l, l')
      UnBlock _             -> mempty
      IsEmpty _ t           -> freeVars' t
      CheckSizeLtSat u      -> freeVars' u
      FindInstance _ cs     -> freeVars' cs
      ResolveInstanceHead q -> mempty
      CheckFunDef{}         -> mempty
      HasBiggerSort s       -> freeVars' s
      HasPTSRule a s        -> freeVars' (a , s)
      CheckLockedVars a b c d -> freeVars' ((a,b),(c,d))
      UnquoteTactic t h g   -> freeVars' (t, (h, g))
      CheckDataSort _ s     -> freeVars' s
      CheckMetaInst m       -> mempty
      CheckType t           -> freeVars' t
      UsableAtModality _ ms mod t -> freeVars' (ms, t)

instance TermLike Constraint where
  foldTerm f = \case
      ValueCmp _ t u v       -> foldTerm f (t, u, v)
      ValueCmpOnFace _ p t u v -> foldTerm f (p, t, u, v)
      ElimCmp _ _ t u es es' -> foldTerm f (t, u, es, es')
      LevelCmp _ l l'        -> foldTerm f (Level l, Level l')  -- Note wrapping as term, to ensure f gets to act on l and l'
      IsEmpty _ t            -> foldTerm f t
      CheckSizeLtSat u       -> foldTerm f u
      UnquoteTactic t h g    -> foldTerm f (t, h, g)
      SortCmp _ s1 s2        -> foldTerm f (Sort s1, Sort s2)   -- Same as LevelCmp case
      UnBlock _              -> mempty
      CheckLockedVars a b c d -> foldTerm f (a, b, c, d)
      FindInstance _ _       -> mempty
      ResolveInstanceHead q  -> mempty
      CheckFunDef{}          -> mempty
      HasBiggerSort s        -> foldTerm f s
      HasPTSRule a s         -> foldTerm f (a, Sort <$> s)
      CheckDataSort _ s      -> foldTerm f s
      CheckMetaInst m        -> mempty
      CheckType t            -> foldTerm f t
      UsableAtModality _ ms m t   -> foldTerm f (Sort <$> ms, t)

  traverseTermM f c = __IMPOSSIBLE__ -- Not yet implemented

instance AllMetas Constraint

data Comparison = CmpEq | CmpLeq
  deriving (Eq, Show, Generic)

instance Pretty Comparison where
  pretty CmpEq  = "="
  pretty CmpLeq = "=<"

-- | An extension of 'Comparison' to @>=@.
data CompareDirection = DirEq | DirLeq | DirGeq
  deriving (Eq, Show)

instance Pretty CompareDirection where
  pretty = text . \case
    DirEq  -> "="
    DirLeq -> "=<"
    DirGeq -> ">="

-- | Embed 'Comparison' into 'CompareDirection'.
fromCmp :: Comparison -> CompareDirection
fromCmp CmpEq  = DirEq
fromCmp CmpLeq = DirLeq

-- | Flip the direction of comparison.
flipCmp :: CompareDirection -> CompareDirection
flipCmp DirEq  = DirEq
flipCmp DirLeq = DirGeq
flipCmp DirGeq = DirLeq

-- | Turn a 'Comparison' function into a 'CompareDirection' function.
--
--   Property: @dirToCmp f (fromCmp cmp) = f cmp@
dirToCmp :: (Comparison -> a -> a -> c) -> CompareDirection -> a -> a -> c
dirToCmp cont DirEq  = cont CmpEq
dirToCmp cont DirLeq = cont CmpLeq
dirToCmp cont DirGeq = flip $ cont CmpLeq

-- | We can either compare two terms at a given type, or compare two
--   types without knowing (or caring about) their sorts.
data CompareAs
  = AsTermsOf Type -- ^ @Type@ should not be @Size@.
                   --   But currently, we do not rely on this invariant.
  | AsSizes        -- ^ Replaces @AsTermsOf Size@.
  | AsTypes
  deriving (Show, Generic)

instance Free CompareAs where
  freeVars' (AsTermsOf a) = freeVars' a
  freeVars' AsSizes       = mempty
  freeVars' AsTypes       = mempty

instance TermLike CompareAs where
  foldTerm f (AsTermsOf a) = foldTerm f a
  foldTerm f AsSizes       = mempty
  foldTerm f AsTypes       = mempty

  traverseTermM f = \case
    AsTermsOf a -> AsTermsOf <$> traverseTermM f a
    AsSizes     -> return AsSizes
    AsTypes     -> return AsTypes

instance AllMetas CompareAs

instance Pretty CompareAs where
  pretty (AsTermsOf a) = ":" <+> pretty a
  pretty AsSizes       = ":" <+> text "Size"
  pretty AsTypes       = empty

---------------------------------------------------------------------------
-- * Open things
---------------------------------------------------------------------------

-- | A thing tagged with the context it came from. Also keeps the substitution from previous
--   checkpoints. This lets us handle the case when an open thing was created in a context that we
--   have since exited. Remember which module it's from to make sure we don't get confused by
--   checkpoints from other files.
data Open a = OpenThing { openThingCheckpoint    :: CheckpointId
                        , openThingCheckpointMap :: Map CheckpointId Substitution
                        , openThingModule        :: ModuleNameHash
                        , openThing              :: a }
    deriving (Show, Functor, Foldable, Traversable, Generic)

instance Decoration Open where
  traverseF f (OpenThing cp env m x) = OpenThing cp env m <$> f x

instance Pretty a => Pretty (Open a) where
  prettyPrec p (OpenThing cp env _ x) = mparens (p > 9) $
    "OpenThing" <+> pretty cp <+> pretty (Map.toList env) <?> prettyPrec 10 x

---------------------------------------------------------------------------
-- * Judgements
--
-- Used exclusively for typing of meta variables.
---------------------------------------------------------------------------

-- | Parametrized since it is used without MetaId when creating a new meta.
data Judgement a
  = HasType
    { jMetaId     :: a
    , jComparison :: Comparison -- ^ are we checking (@CmpLeq@) or inferring (@CmpEq@) the type?
    , jMetaType   :: Type
    }
  | IsSort
    { jMetaId   :: a
    , jMetaType :: Type -- Andreas, 2011-04-26: type needed for higher-order sort metas
    }
  deriving (Show, Generic)

instance Pretty a => Pretty (Judgement a) where
    pretty (HasType a cmp t) = hsep [ pretty a, ":"    , pretty t ]
    pretty (IsSort  a t)     = hsep [ pretty a, ":sort", pretty t ]

-----------------------------------------------------------------------------
-- ** Generalizable variables
-----------------------------------------------------------------------------

data DoGeneralize
  = YesGeneralizeVar  -- ^ Generalize because it is a generalizable variable.
  | YesGeneralizeMeta -- ^ Generalize because it is a metavariable and
                      --   we're currently checking the type of a generalizable variable
                      --   (this should get the default modality).
  | NoGeneralize      -- ^ Don't generalize.
  deriving (Eq, Ord, Show, Generic)

-- | The value of a generalizable variable. This is created to be a
--   generalizable meta before checking the type to be generalized.
data GeneralizedValue = GeneralizedValue
  { genvalCheckpoint :: CheckpointId
  , genvalTerm       :: Term
  , genvalType       :: Type
  } deriving (Show, Generic)

---------------------------------------------------------------------------
-- ** Meta variables
---------------------------------------------------------------------------

-- | Information about local meta-variables.

data MetaVariable =
        MetaVar { mvInfo          :: MetaInfo
                , mvPriority      :: MetaPriority -- ^ some metavariables are more eager to be instantiated
                , mvPermutation   :: Permutation
                  -- ^ a metavariable doesn't have to depend on all variables
                  --   in the context, this "permutation" will throw away the
                  --   ones it does not depend on
                , mvJudgement     :: Judgement MetaId
                , mvInstantiation :: MetaInstantiation
                , mvListeners     :: Set Listener -- ^ meta variables scheduled for eta-expansion but blocked by this one
                , mvFrozen        :: Frozen -- ^ are we past the point where we can instantiate this meta variable?
                , mvTwin          :: Maybe MetaId
                  -- ^ @Just m@ means that this meta-variable will be
                  -- equated to @m@ when the latter is unblocked. See
                  -- 'Agda.TypeChecking.MetaVars.blockTermOnProblem'.
                }
  deriving Generic

data Listener = EtaExpand MetaId
              | CheckConstraint Nat ProblemConstraint
  deriving Generic

instance Eq Listener where
  EtaExpand       x   == EtaExpand       y   = x == y
  CheckConstraint x _ == CheckConstraint y _ = x == y
  _ == _ = False

instance Ord Listener where
  EtaExpand       x   `compare` EtaExpand       y   = x `compare` y
  CheckConstraint x _ `compare` CheckConstraint y _ = x `compare` y
  EtaExpand{} `compare` CheckConstraint{} = LT
  CheckConstraint{} `compare` EtaExpand{} = GT

-- | Frozen meta variable cannot be instantiated by unification.
--   This serves to prevent the completion of a definition by its use
--   outside of the current block.
--   (See issues 118, 288, 399).
data Frozen
  = Frozen        -- ^ Do not instantiate.
  | Instantiable
    deriving (Eq, Show, Generic)

data MetaInstantiation
        = InstV Instantiation -- ^ solved
        | Open                -- ^ unsolved
        | OpenInstance        -- ^ open, to be instantiated by instance search
        | BlockedConst Term   -- ^ solution blocked by unsolved constraints
        | PostponedTypeCheckingProblem (Closure TypeCheckingProblem)
  deriving Generic

-- | Meta-variable instantiations.

data Instantiation = Instantiation
  { instTel :: [Arg String]
    -- ^ The solution is abstracted over these free variables.
  , instBody :: Term
    -- ^ The body of the solution.
  }
  deriving (Show, Generic)

-- | Information about remote meta-variables.
--
-- Remote meta-variables are meta-variables originating in other
-- modules. These meta-variables are always instantiated. We do not
-- retain all the information about a local meta-variable when
-- creating an interface:
--
-- * The 'mvPriority' field is not needed, because the meta-variable
--   cannot be instantiated.
-- * The 'mvFrozen' field is not needed, because there is no point in
--   freezing instantiated meta-variables.
-- * The 'mvListeners' field is not needed, because no meta-variable
--   should be listening to this one.
-- * The 'mvTwin' field is not needed, because the meta-variable has
--   already been instantiated.
-- * The 'mvPermutation' is currently removed, but could be retained
--   if it turns out to be useful for something.
-- * The only part of the 'mvInfo' field that is kept is the
--   'miModality' field. The 'miMetaOccursCheck' and 'miGeneralizable'
--   fields are omitted, because the meta-variable has already been
--   instantiated. The 'Range' that is part of the 'miClosRange' field
--   and the 'miNameSuggestion' field are omitted because instantiated
--   meta-variables are typically not presented to users. Finally the
--   'Closure' part of the 'miClosRange' field is omitted because it
--   can be large (at least if we ignore potential sharing).

data RemoteMetaVariable = RemoteMetaVariable
  { rmvInstantiation :: Instantiation
  , rmvModality      :: Modality
  , rmvJudgement     :: Judgement MetaId
  }
  deriving (Show, Generic)

-- | Solving a 'CheckArgs' constraint may or may not check the target type. If
--   it did, it returns a handle to any unsolved constraints.
data CheckedTarget = CheckedTarget (Maybe ProblemId)
                   | NotCheckedTarget

data PrincipalArgTypeMetas = PrincipalArgTypeMetas
  { patmMetas     :: Args -- ^ metas created for hidden and instance arguments
                          --   in the principal argument's type
  , patmRemainder :: Type -- ^ principal argument's type, stripped of hidden and
                          --   instance arguments
  }
  deriving Generic

data TypeCheckingProblem
  = CheckExpr Comparison A.Expr Type
  | CheckArgs Comparison ExpandHidden Range [NamedArg A.Expr] Type Type (ArgsCheckState CheckedTarget -> TCM Term)
  | CheckProjAppToKnownPrincipalArg Comparison A.Expr ProjOrigin (List1 QName) A.Args Type Int Term Type PrincipalArgTypeMetas
  | CheckLambda Comparison (Arg (List1 (WithHiding Name), Maybe Type)) A.Expr Type
    -- ^ @(λ (xs : t₀) → e) : t@
    --   This is not an instance of 'CheckExpr' as the domain type
    --   has already been checked.
    --   For example, when checking
    --     @(λ (x y : Fin _) → e) : (x : Fin n) → ?@
    --   we want to postpone @(λ (y : Fin n) → e) : ?@ where @Fin n@
    --   is a 'Type' rather than an 'A.Expr'.
  | DoQuoteTerm Comparison Term Type -- ^ Quote the given term and check type against `Term`
  deriving Generic

instance Pretty MetaInstantiation where
  pretty = \case
    Open                                     -> "Open"
    OpenInstance                             -> "OpenInstance"
    PostponedTypeCheckingProblem{}           -> "PostponedTypeCheckingProblem (...)"
    BlockedConst t                           -> hsep [ "BlockedConst", parens (pretty t) ]
    InstV Instantiation{ instTel, instBody } -> hsep [ "InstV", pretty instTel, parens (pretty instBody) ]

-- | Meta variable priority:
--   When we have an equation between meta-variables, which one
--   should be instantiated?
--
--   Higher value means higher priority to be instantiated.
newtype MetaPriority = MetaPriority Int
    deriving (Eq, Ord, Show, NFData)

data RunMetaOccursCheck
  = RunMetaOccursCheck
  | DontRunMetaOccursCheck
  deriving (Eq, Ord, Show, Generic)

-- | @MetaInfo@ is cloned from one meta to the next during pruning.
data MetaInfo = MetaInfo
  { miClosRange       :: Closure Range -- TODO: Not so nice. But we want both to have the environment of the meta (Closure) and its range.
  , miModality        :: Modality           -- ^ Instantiable with irrelevant/erased solution?
  , miMetaOccursCheck :: RunMetaOccursCheck -- ^ Run the extended occurs check that goes in definitions?
  , miNameSuggestion  :: MetaNameSuggestion
    -- ^ Used for printing.
    --   @Just x@ if meta-variable comes from omitted argument with name @x@.
  , miGeneralizable   :: Arg DoGeneralize
    -- ^ Should this meta be generalized if unsolved? If so, at what ArgInfo?
  }
  deriving Generic

instance LensModality MetaInfo where
  getModality = miModality
  setModality mod mi = mi { miModality = mod }
  mapModality f mi = mi { miModality = f $ miModality mi }

instance LensQuantity MetaInfo where
  getQuantity   = getQuantity . getModality
  mapQuantity f = mapModality (mapQuantity f)

instance LensRelevance MetaInfo where
  mapRelevance f = mapModality (mapRelevance f)

-- | Name suggestion for meta variable.  Empty string means no suggestion.
type MetaNameSuggestion = String

-- | For printing, we couple a meta with its name suggestion.
data NamedMeta = NamedMeta
  { nmSuggestion :: MetaNameSuggestion
  , nmid         :: MetaId
  }

-- | Append an 'ArgName' to a 'MetaNameSuggestion', for computing the
-- name suggestions of eta-expansion metas. If the 'MetaNameSuggestion'
-- is empty or an underscore, the field name is taken as the suggestion.
suffixNameSuggestion :: MetaNameSuggestion -> ArgName -> MetaNameSuggestion
suffixNameSuggestion "_"    field = field
suffixNameSuggestion ""     field = field
suffixNameSuggestion record field = record ++ "." ++ field

instance Pretty NamedMeta where
  pretty (NamedMeta "" x) = pretty x
  pretty (NamedMeta "_" x) = pretty x
  pretty (NamedMeta s  x) = text $ "_" ++ s ++ prettyShow x

-- | Used for meta-variables from the current module.

type LocalMetaStore = Map MetaId MetaVariable

{-# SPECIALIZE Map.insert :: MetaId -> v -> Map MetaId v -> Map MetaId v #-}
{-# SPECIALIZE Map.lookup :: MetaId -> Map MetaId v -> Maybe v #-}

-- | Used for meta-variables from other modules (and in 'Interface's).

type RemoteMetaStore = HashMap MetaId RemoteMetaVariable

instance HasRange MetaInfo where
  getRange = clValue . miClosRange

instance HasRange MetaVariable where
    getRange m = getRange $ getMetaInfo m

instance SetRange MetaInfo where
  setRange r m = m { miClosRange = (miClosRange m) { clValue = r }}

instance SetRange MetaVariable where
  setRange r m = m { mvInfo = setRange r (mvInfo m) }

instance LensModality MetaVariable where
  getModality = getModality . mvInfo
  setModality mod mv = mv { mvInfo = setModality mod $ mvInfo mv }
  mapModality f mv = mv { mvInfo = mapModality f $ mvInfo mv }

instance LensRelevance MetaVariable where
  setRelevance mod mv = mv { mvInfo = setRelevance mod $ mvInfo mv }

instance LensQuantity MetaVariable where
  getQuantity   = getQuantity . getModality
  mapQuantity f = mapModality (mapQuantity f)

instance LensModality RemoteMetaVariable where
  getModality      = rmvModality
  mapModality f mv = mv { rmvModality = f $ rmvModality mv }

instance LensRelevance RemoteMetaVariable where
  mapRelevance f = mapModality (mapRelevance f)

instance LensQuantity RemoteMetaVariable where
  mapQuantity f = mapModality (mapQuantity f)

normalMetaPriority :: MetaPriority
normalMetaPriority = MetaPriority 0

lowMetaPriority :: MetaPriority
lowMetaPriority = MetaPriority (-10)

highMetaPriority :: MetaPriority
highMetaPriority = MetaPriority 10

getMetaInfo :: MetaVariable -> Closure Range
getMetaInfo = miClosRange . mvInfo

getMetaScope :: MetaVariable -> ScopeInfo
getMetaScope m = clScope $ getMetaInfo m

getMetaEnv :: MetaVariable -> TCEnv
getMetaEnv m = clEnv $ getMetaInfo m

getMetaSig :: MetaVariable -> Signature
getMetaSig m = clSignature $ getMetaInfo m

-- Lenses

metaFrozen :: Lens' MetaVariable Frozen
metaFrozen f mv = f (mvFrozen mv) <&> \ x -> mv { mvFrozen = x }

_mvInfo :: Lens' MetaVariable MetaInfo
_mvInfo f mv = (f $! mvInfo mv) <&> \ mi -> mv { mvInfo = mi }

-- Lenses onto Closure Range

instance LensClosure MetaInfo Range where
  lensClosure f mi = (f $! miClosRange mi) <&> \ cl -> mi { miClosRange = cl }

instance LensClosure MetaVariable Range where
  lensClosure = _mvInfo . lensClosure

-- Lenses onto IsAbstract

instance LensIsAbstract TCEnv where
  lensIsAbstract f env =
     -- Andreas, 2019-08-19
     -- Using $! to prevent space leaks like #1829.
     -- This can crash when trying to get IsAbstract from IgnoreAbstractMode.
    (f $! fromMaybe __IMPOSSIBLE__ (aModeToDef $ envAbstractMode env))
    <&> \ a -> env { envAbstractMode = aDefToMode a }

instance LensIsAbstract (Closure a) where
  lensIsAbstract = lensTCEnv . lensIsAbstract

instance LensIsAbstract MetaInfo where
  lensIsAbstract = lensClosure . lensIsAbstract

instance LensIsOpaque TCEnv where
  lensIsOpaque f env =
    (f $! case envCurrentOpaqueId env of { Just x -> OpaqueDef x ; Nothing -> TransparentDef })
    <&> \case { OpaqueDef x    -> env { envCurrentOpaqueId = Just x }
              ; TransparentDef -> env { envCurrentOpaqueId = Nothing }
              }

---------------------------------------------------------------------------
-- ** Interaction meta variables
---------------------------------------------------------------------------

-- | Interaction points are created by the scope checker who sets the range.
--   The meta variable is created by the type checker and then hooked up to the
--   interaction point.
data InteractionPoint = InteractionPoint
  { ipRange    :: Range        -- ^ The position of the interaction point.
  , ipMeta     :: Maybe MetaId -- ^ The meta variable, if any, holding the type etc.
  , ipSolved   :: Bool         -- ^ Has this interaction point already been solved?
  , ipClause   :: IPClause
    -- ^ The clause of the interaction point (if any).
    --   Used for case splitting.
  , ipBoundary :: IPBoundary
  }
  deriving Generic

instance Eq InteractionPoint where (==) = (==) `on` ipMeta

instance HasTag InteractionPoint where
  type Tag InteractionPoint = MetaId
  tag = ipMeta

-- | Data structure managing the interaction points.
--
--   We never remove interaction points from this map, only set their
--   'ipSolved' to @True@.  (Issue #2368)
type InteractionPoints = BiMap InteractionId InteractionPoint

-- | Flag to indicate whether the meta is overapplied in the
--   constraint.  A meta is overapplied if it has more arguments than
--   the size of the telescope in its creation environment
--   (as stored in MetaInfo).
data Overapplied = Overapplied | NotOverapplied
  deriving (Eq, Show, Generic)

-- | Datatype representing a single boundary condition:
--   x_0 = u_0, ... ,x_n = u_n ⊢ t = ?n es
data IPFace' t = IPFace'
  { faceEqns :: [(t, t)]
  , faceRHS  :: t
  }

newtype IPBoundary' t = IPBoundary
  { getBoundary :: Map (IntMap Bool) t
  }
  deriving (Show, Functor, Foldable, Traversable, Generic)

type IPBoundary = IPBoundary' Term

-- | Which clause is an interaction point located in?
data IPClause = IPClause
  { ipcQName    :: QName              -- ^ The name of the function.
  , ipcClauseNo :: Int                -- ^ The number of the clause of this function.
  , ipcType     :: Type               -- ^ The type of the function
  , ipcWithSub  :: Maybe Substitution -- ^ Module parameter substitution
  , ipcClause   :: A.SpineClause      -- ^ The original AST clause.
  , ipcClosure  :: Closure ()         -- ^ Environment for rechecking the clause.
  }
  | IPNoClause -- ^ The interaction point is not in the rhs of a clause.
  deriving (Generic)

instance Eq IPClause where
  IPNoClause           == IPNoClause             = True
  IPClause x i _ _ _ _ == IPClause x' i' _ _ _ _ = x == x' && i == i'
  _                    == _                      = False

---------------------------------------------------------------------------
-- ** Signature
---------------------------------------------------------------------------

data Signature = Sig
      { _sigSections    :: Sections
      , _sigDefinitions :: Definitions
      , _sigRewriteRules:: RewriteRuleMap  -- ^ The rewrite rules defined in this file.
      }
  deriving (Show, Generic)

sigSections :: Lens' Signature Sections
sigSections f s =
  f (_sigSections s) <&>
  \x -> s {_sigSections = x}

sigDefinitions :: Lens' Signature Definitions
sigDefinitions f s =
  f (_sigDefinitions s) <&>
  \x -> s {_sigDefinitions = x}

sigRewriteRules :: Lens' Signature RewriteRuleMap
sigRewriteRules f s =
  f (_sigRewriteRules s) <&>
  \x -> s {_sigRewriteRules = x}

type Sections    = Map ModuleName Section
type Definitions = HashMap QName Definition
type RewriteRuleMap = HashMap QName RewriteRules
type DisplayForms = HashMap QName [LocalDisplayForm]

-- 2023-21-30, András: see issue 6927
#if __GLASGOW_HASKELL__ >= 900
{-# SPECIALIZE HMap.insert :: QName -> v -> HashMap QName v -> HashMap QName v #-}
#endif
{-# SPECIALIZE HMap.lookup :: QName -> HashMap QName v -> Maybe v #-}

newtype Section = Section { _secTelescope :: Telescope }
  deriving (Show, NFData)

instance Pretty Section where
  pretty = pretty . _secTelescope

secTelescope :: Lens' Section Telescope
secTelescope f s =
  f (_secTelescope s) <&>
  \x -> s {_secTelescope = x}

emptySignature :: Signature
emptySignature = Sig Map.empty HMap.empty HMap.empty

-- | A @DisplayForm@ is in essence a rewrite rule @q ts --> dt@ for a defined symbol (could be a
--   constructor as well) @q@. The right hand side is a 'DisplayTerm' which is used to 'reify' to a
--   more readable 'Abstract.Syntax'.
--
--   The patterns @ts@ are just terms, but the first @dfPatternVars@ variables are pattern variables
--   that matches any term.
data DisplayForm = Display
  { dfPatternVars :: Nat
    -- ^ Number @n@ of pattern variables in 'dfPats'.
  , dfPats :: Elims
    -- ^ Left hand side patterns, the @n@ first free variables are pattern variables,
    --   any variables above @n@ are fixed and only match that particular variable. This
    --   happens when you have display forms inside parameterised modules that match on the module
    --   parameters. The 'ArgInfo' is ignored in these patterns.
  , dfRHS :: DisplayTerm
    -- ^ Right hand side.
  }
  deriving (Show, Generic)

type LocalDisplayForm = Open DisplayForm

-- | A structured presentation of a 'Term' for reification into
--   'Abstract.Syntax'.
data DisplayTerm
  = DWithApp DisplayTerm [DisplayTerm] Elims
    -- ^ @(f vs | ws) es@.
    --   The first 'DisplayTerm' is the parent function @f@ with its args @vs@.
    --   The list of 'DisplayTerm's are the with expressions @ws@.
    --   The 'Elims' are additional arguments @es@
    --   (possible in case the with-application is of function type)
    --   or projections (if it is of record type).
  | DCon ConHead ConInfo [Arg DisplayTerm]
    -- ^ @c vs@.
  | DDef QName [Elim' DisplayTerm]
    -- ^ @d vs@.
  | DDot' Term Elims
    -- ^ @.(v es)@.  See 'DTerm''.
  | DTerm' Term Elims
    -- ^ @v es@.
    --   This is a frozen elimination that is not always safe to run,
    --   because display forms may be ill-typed.
    --   (See issue #6476.)
  deriving (Show, Generic)

pattern DDot :: Term -> DisplayTerm
pattern DDot v = DDot' v []

pattern DTerm :: Term -> DisplayTerm
pattern DTerm v = DTerm' v []

instance Free DisplayForm where
  freeVars' (Display n ps t) = underBinder (freeVars' ps) `mappend` underBinder' n (freeVars' t)

instance Free DisplayTerm where
  freeVars' (DWithApp t ws es) = freeVars' (t, (ws, es))
  freeVars' (DCon _ _ vs)      = freeVars' vs
  freeVars' (DDef _ es)        = freeVars' es
  freeVars' (DDot' v es)       = freeVars' (v, es)
  freeVars' (DTerm' v es)      = freeVars' (v, es)

instance Pretty DisplayTerm where
  prettyPrec p v =
    case v of
      DTerm v           -> prettyPrec p v
      DTerm' v es       -> prettyPrec 9 v `pApp` es
      DDot v            -> "." <> prettyPrec 10 v
      DDot' v es        -> "." <> parens (prettyPrec 9 v `pAp` es)
      DDef f es        -> pretty f `pApp` es
      DCon c _ vs      -> pretty (conName c) `pApp` map Apply vs
      DWithApp h ws es ->
        mparens (p > 0)
          (sep [ pretty h
              , nest 2 $ fsep [ "|" <+> pretty w | w <- ws ] ])
        `pApp` es
    where
      pApp :: Pretty el => Doc -> [el] -> Doc
      pApp d els = mparens (not (null els) && p > 9) $ pAp d els
      pAp :: Pretty el => Doc -> [el] -> Doc
      pAp d els = sep [d, nest 2 $ fsep (map (prettyPrec 10) els)]

instance Pretty DisplayForm where
  prettyPrec p (Display fv lhs rhs) = mparens (p > 9) $
    "Display" <?> fsep [ pshow fv, prettyPrec 10 lhs, prettyPrec 10 rhs ]

-- | By default, we have no display form.
defaultDisplayForm :: QName -> [LocalDisplayForm]
defaultDisplayForm c = []

-- | Non-linear (non-constructor) first-order pattern.
data NLPat
  = PVar !Int [Arg Int]
    -- ^ Matches anything (modulo non-linearity) that only contains bound
    --   variables that occur in the given arguments.
  | PDef QName PElims
    -- ^ Matches @f es@
  | PLam ArgInfo (Abs NLPat)
    -- ^ Matches @λ x → t@
  | PPi (Dom NLPType) (Abs NLPType)
    -- ^ Matches @(x : A) → B@
  | PSort NLPSort
    -- ^ Matches a sort of the given shape.
  | PBoundVar {-# UNPACK #-} !Int PElims
    -- ^ Matches @x es@ where x is a lambda-bound variable
  | PTerm Term
    -- ^ Matches the term modulo β (ideally βη).
  deriving (Show, Generic)
type PElims = [Elim' NLPat]

type instance TypeOf NLPat = Type
type instance TypeOf [Elim' NLPat] = (Type, Elims -> Term)

instance TermLike NLPat where
  traverseTermM f = \case
    p@PVar{}       -> return p
    PDef d ps      -> PDef d <$> traverseTermM f ps
    PLam i p       -> PLam i <$> traverseTermM f p
    PPi a b        -> PPi <$> traverseTermM f a <*> traverseTermM f b
    PSort s        -> PSort <$> traverseTermM f s
    PBoundVar i ps -> PBoundVar i <$> traverseTermM f ps
    PTerm t        -> PTerm <$> f t

  foldTerm f t = case t of
    PVar{}         -> mempty
    PDef d ps      -> foldTerm f ps
    PLam i p       -> foldTerm f p
    PPi a b        -> foldTerm f (a, b)
    PSort s        -> foldTerm f s
    PBoundVar i ps -> foldTerm f ps
    PTerm t        -> foldTerm f t

instance AllMetas NLPat

data NLPType = NLPType
  { nlpTypeSort :: NLPSort
  , nlpTypeUnEl :: NLPat
  } deriving (Show, Generic)

instance TermLike NLPType where
  traverseTermM f (NLPType s t) = NLPType <$> traverseTermM f s <*> traverseTermM f t

  foldTerm f (NLPType s t) = foldTerm f (s, t)

instance AllMetas NLPType

data NLPSort
  = PUniv Univ NLPat
  | PInf Univ Integer
  | PSizeUniv
  | PLockUniv
  | PLevelUniv
  | PIntervalUniv
  deriving (Show, Generic)

pattern PType, PProp, PSSet :: NLPat -> NLPSort
pattern PType p = PUniv UType p
pattern PProp p = PUniv UProp p
pattern PSSet p = PUniv USSet p

{-# COMPLETE
  PType, PSSet, PProp, PInf,
  PSizeUniv, PLockUniv, PLevelUniv, PIntervalUniv #-}

instance TermLike NLPSort where
  traverseTermM f = \case
    PUniv u p         -> PUniv u <$> traverseTermM f p
    s@PInf{}          -> return s
    s@PSizeUniv{}     -> return s
    s@PLockUniv{}     -> return s
    s@PLevelUniv{}    -> return s
    s@PIntervalUniv{} -> return s

  foldTerm f t = case t of
    PUniv _ p         -> foldTerm f p
    s@PInf{}          -> mempty
    s@PSizeUniv{}     -> mempty
    s@PLockUniv{}     -> mempty
    s@PLevelUniv{}    -> mempty
    s@PIntervalUniv{} -> mempty

instance AllMetas NLPSort

type RewriteRules = [RewriteRule]

-- | Rewrite rules can be added independently from function clauses.
data RewriteRule = RewriteRule
  { rewName    :: QName      -- ^ Name of rewrite rule @q : Γ → f ps ≡ rhs@
                             --   where @≡@ is the rewrite relation.
  , rewContext :: Telescope  -- ^ @Γ@.
  , rewHead    :: QName      -- ^ @f@.
  , rewPats    :: PElims     -- ^ @Γ ⊢ f ps : t@.
  , rewRHS     :: Term       -- ^ @Γ ⊢ rhs : t@.
  , rewType    :: Type       -- ^ @Γ ⊢ t@.
  , rewFromClause :: Bool    -- ^ Was this rewrite rule created from a clause in the definition of the function?
  }
    deriving (Show, Generic)

data Definition = Defn
  { defArgInfo        :: ArgInfo -- ^ Hiding should not be used.
  , defName           :: QName   -- ^ The canonical name, used e.g. in compilation.
  , defType           :: Type    -- ^ Type of the lifted definition.
  , defSizedType      :: Maybe SizeSignature -- ^ Size annotation for the type. Used in type-based termination checking.
  , defPolarity       :: [Polarity]
    -- ^ Variance information on arguments of the definition.
    --   Does not include info for dropped parameters to
    --   projection(-like) functions and constructors.
  , defArgOccurrences :: [Occurrence]
    -- ^ Positivity information on arguments of the definition.
    --   Does not include info for dropped parameters to
    --   projection(-like) functions and constructors.

    --   Sometimes Agda looks up 'Occurrence's in these lists based on
    --   their position, so one might consider replacing the list
    --   with, say, an 'IntMap'. However, presumably these lists tend
    --   to be short, in which case 'IntMap's could be slower than
    --   lists. For instance, at one point the longest list
    --   encountered for the standard library (in serialised
    --   interfaces) had length 27. Distribution:
    --
    --   Length, number of lists
    --   -----------------------
    --
    --    0, 2444
    --    1,  721
    --    2,  433
    --    3,  668
    --    4,  602
    --    5,  624
    --    6,  626
    --    7,  484
    --    8,  375
    --    9,  264
    --   10,  305
    --   11,  188
    --   12,  171
    --   13,  108
    --   14,   84
    --   15,   80
    --   16,   38
    --   17,   23
    --   18,   16
    --   19,    8
    --   20,    7
    --   21,    5
    --   22,    2
    --   23,    3
    --   27,    1

  , defArgGeneralizable :: NumGeneralizableArgs
    -- ^ For a generalized variable, shows how many arguments should be generalised.
  , defGeneralizedParams :: [Maybe Name]
    -- ^ Gives the name of the (bound variable) parameter for named generalized
    --   parameters. This is needed to bring it into scope when type checking
    --   the data/record definition corresponding to a type with generalized
    --   parameters.
  , defDisplay        :: [LocalDisplayForm]
  , defMutual         :: MutualId
  , defCompiledRep    :: CompiledRepresentation
  , defInstance       :: Maybe QName
    -- ^ @Just q@ when this definition is an instance of class q
  , defCopy           :: Bool
    -- ^ Has this function been created by a module
                         -- instantiation?
  , defMatchable      :: Set QName
    -- ^ The set of symbols with rewrite rules that match against this symbol
  , defNoCompilation  :: Bool
    -- ^ should compilers skip this? Used for e.g. cubical's comp
  , defInjective      :: Bool
    -- ^ Should the def be treated as injective by the pattern matching unifier?
  , defCopatternLHS   :: Bool
    -- ^ Is this a function defined by copatterns?
  , defBlocked        :: Blocked_
    -- ^ What blocking tag to use when we cannot reduce this def?
    --   Used when checking a function definition is blocked on a meta
    --   in the type.
  , defLanguage       :: !Language
    -- ^ The language used for the definition.
  , theDef            :: Defn
  }
    deriving (Show, Generic)

instance LensArgInfo Definition where
  getArgInfo = defArgInfo
  mapArgInfo f def = def { defArgInfo = f $ defArgInfo def }

instance LensModality  Definition where
instance LensQuantity  Definition where
instance LensRelevance Definition where

data NumGeneralizableArgs
  = NoGeneralizableArgs
  | SomeGeneralizableArgs !Int
    -- ^ When lambda-lifting new args are generalizable if
    --   'SomeGeneralizableArgs', also when the number is zero.
  deriving Show

lensTheDef :: Lens' Definition Defn
lensTheDef f d = f (theDef d) <&> \ df -> d { theDef = df }

-- | Create a definition with sensible defaults.
defaultDefn ::
  ArgInfo -> QName -> Type -> Language -> Defn -> Definition
defaultDefn info x t lang def = Defn
  { defArgInfo        = info
  , defName           = x
  , defType           = t
  , defSizedType      = Nothing
  , defPolarity       = []
  , defArgOccurrences = []
  , defArgGeneralizable = NoGeneralizableArgs
  , defGeneralizedParams = []
  , defDisplay        = defaultDisplayForm x
  , defMutual         = 0
  , defCompiledRep    = noCompiledRep
  , defInstance       = Nothing
  , defCopy           = False
  , defMatchable      = Set.empty
  , defNoCompilation  = False
  , defInjective      = False
  , defCopatternLHS   = False
  , defBlocked        = NotBlocked ReallyNotBlocked ()
  , defLanguage       = lang
  , theDef            = def
  }

-- | Polarity for equality and subtype checking.
data Polarity
  = Covariant      -- ^ monotone
  | Contravariant  -- ^ antitone
  | Invariant      -- ^ no information (mixed variance)
  | Nonvariant     -- ^ constant
  deriving (Show, Eq, Generic)

instance Pretty Polarity where
  pretty = text . \case
    Covariant     -> "+"
    Contravariant -> "-"
    Invariant     -> "*"
    Nonvariant    -> "_"

-- | Information about whether an argument is forced by the type of a function.
data IsForced
  = Forced
  | NotForced
  deriving (Show, Eq, Generic)

-- | The backends are responsible for parsing their own pragmas.
data CompilerPragma = CompilerPragma Range String
  deriving (Show, Eq, Generic)

instance HasRange CompilerPragma where
  getRange (CompilerPragma r _) = r

type BackendName    = String

jsBackendName, ghcBackendName :: BackendName
jsBackendName  = "JS"
ghcBackendName = "GHC"

type CompiledRepresentation = Map BackendName [CompilerPragma]

noCompiledRep :: CompiledRepresentation
noCompiledRep = Map.empty

-- A face represented as a list of equality constraints.
-- (r,False) ↦ (r = i0)
-- (r,True ) ↦ (r = i1)
type Face = [(Term,Bool)]

-- | An alternative representation of partial elements in a telescope:
--   Γ ⊢ λ Δ. [φ₁ u₁, ... , φₙ uₙ] : Δ → PartialP (∨_ᵢ φᵢ) T
--   see cubicaltt paper (however we do not store the type T).
data System = System
  { systemTel :: Telescope
    -- ^ the telescope Δ, binding vars for the clauses, Γ ⊢ Δ
  , systemClauses :: [(Face,Term)]
    -- ^ a system [φ₁ u₁, ... , φₙ uₙ] where Γ, Δ ⊢ φᵢ and Γ, Δ, φᵢ ⊢ uᵢ
  } deriving (Show, Generic)

-- | Additional information for extended lambdas.
data ExtLamInfo = ExtLamInfo
  { extLamModule    :: ModuleName
    -- ^ For complicated reasons the scope checker decides the QName of a
    --   pattern lambda, and thus its module. We really need to decide the
    --   module during type checking though, since if the lambda appears in a
    --   refined context the module picked by the scope checker has very much
    --   the wrong parameters.
  , extLamAbsurd :: Bool
    -- ^ Was this definition created from an absurd lambda @λ ()@?
  , extLamSys :: !(Strict.Maybe System)
  } deriving (Show, Generic)

modifySystem :: (System -> System) -> ExtLamInfo -> ExtLamInfo
modifySystem f e = let !e' = e { extLamSys = f <$> extLamSys e } in e'

-- | Additional information for projection 'Function's.
data Projection = Projection
  { projProper    :: Maybe QName
    -- ^ @Nothing@ if only projection-like, @Just r@ if record projection.
    --   The @r@ is the name of the record type projected from.
    --   This field is updated by module application.
  , projOrig      :: QName
    -- ^ The original projection name
    --   (current name could be from module application).
  , projFromType  :: Arg QName
    -- ^ Type projected from. Original record type if @projProper = Just{}@.
    --   Also stores @ArgInfo@ of the principal argument.
    --   This field is unchanged by module application.
  , projIndex     :: Int
    -- ^ Index of the record argument.
    --   Start counting with 1, because 0 means that
    --   it is already applied to the record value.
    --   This can happen in module instantiation, but
    --   then either the record value is @var 0@, or @funProjection == Nothing@.
  , projLams :: ProjLams
    -- ^ Term @t@ to be be applied to record parameters and record value.
    --   The parameters will be dropped.
    --   In case of a proper projection, a postfix projection application
    --   will be created: @t = \ pars r -> r .p@
    --   (Invariant: the number of abstractions equals 'projIndex'.)
    --   In case of a projection-like function, just the function symbol
    --   is returned as 'Def':  @t = \ pars -> f@.
  } deriving (Show, Generic)

-- | Abstractions to build projection function (dropping parameters).
newtype ProjLams = ProjLams { getProjLams :: [Arg ArgName] }
  deriving (Show, Null, Generic)

-- | Building the projection function (which drops the parameters).
projDropPars :: Projection -> ProjOrigin -> Term
-- Proper projections:
projDropPars (Projection Just{} d _ _ lams) o =
  case initLast $ getProjLams lams of
    Nothing -> Def d []
    Just (pars, Arg i y) ->
      let core = Lam i $ Abs y $ Var 0 [Proj o d] in
      List.foldr (\ (Arg ai x) -> Lam ai . NoAbs x) core pars
-- Projection-like functions:
projDropPars (Projection Nothing d _ _ lams) o =
  List.foldr (\ (Arg ai x) -> Lam ai . NoAbs x) (Def d []) $
    initWithDefault __IMPOSSIBLE__ $ getProjLams lams

-- | The info of the principal (record) argument.
projArgInfo :: Projection -> ArgInfo
projArgInfo (Projection _ _ _ _ lams) =
  maybe __IMPOSSIBLE__ getArgInfo $ lastMaybe $ getProjLams lams

-- | Should a record type admit eta-equality?
data EtaEquality
  = Specified { theEtaEquality :: !HasEta }  -- ^ User specifed 'eta-equality' or 'no-eta-equality'.
  | Inferred  { theEtaEquality :: !HasEta }  -- ^ Positivity checker inferred whether eta is safe.
  deriving (Show, Eq, Generic)

instance PatternMatchingAllowed EtaEquality where
  patternMatchingAllowed = patternMatchingAllowed . theEtaEquality

instance CopatternMatchingAllowed EtaEquality where
  copatternMatchingAllowed = copatternMatchingAllowed . theEtaEquality

-- | Make sure we do not overwrite a user specification.
setEtaEquality :: EtaEquality -> HasEta -> EtaEquality
setEtaEquality e@Specified{} _ = e
setEtaEquality _ b = Inferred b

data FunctionFlag
  = FunStatic  -- ^ Should calls to this function be normalised at compile-time?
  | FunInline  -- ^ Should calls to this function be inlined by the compiler?
  | FunMacro   -- ^ Is this function a macro?
  deriving (Eq, Ord, Enum, Show, Generic)

data CompKit = CompKit
  { nameOfHComp :: Maybe QName
  , nameOfTransp :: Maybe QName
  }
  deriving (Eq, Ord, Show, Generic)

emptyCompKit :: CompKit
emptyCompKit = CompKit Nothing Nothing

defaultAxiom :: Defn
defaultAxiom = Axiom False

constTranspAxiom :: Defn
constTranspAxiom = Axiom True

data Defn
  = AxiomDefn AxiomData
      -- ^ Postulate.
  | DataOrRecSigDefn DataOrRecSigData
      -- ^ Data or record type signature that doesn't yet have a definition.
  | GeneralizableVar
      -- ^ Generalizable variable (introduced in `generalize` block).
  | AbstractDefn Defn
      -- ^ Returned by 'getConstInfo' if definition is abstract.
  | FunctionDefn FunctionData
  | DatatypeDefn DatatypeData
  | RecordDefn RecordData
  | ConstructorDefn ConstructorData
  | PrimitiveDefn PrimitiveData
      -- ^ Primitive or builtin functions.
  | PrimitiveSortDefn PrimitiveSortData
    deriving (Show, Generic)

{-# COMPLETE
  Axiom, DataOrRecSig, GeneralizableVar, AbstractDefn,
  Function, Datatype, Record, Constructor, Primitive, PrimitiveSort #-}

data AxiomData = AxiomData
  { _axiomConstTransp :: Bool
    -- ^ Can transp for this postulate be constant?
    --   Set to @True@ for bultins like String.
  } deriving (Show, Generic)

pattern Axiom :: Bool -> Defn
pattern Axiom{ axiomConstTransp } = AxiomDefn (AxiomData axiomConstTransp)

data DataOrRecSigData = DataOrRecSigData
  { _datarecPars :: Int
  } deriving (Show, Generic)

pattern DataOrRecSig :: Int -> Defn
pattern DataOrRecSig{ datarecPars } = DataOrRecSigDefn (DataOrRecSigData datarecPars)

-- | Indicates the reason behind a function having not been marked
-- projection-like.
data ProjectionLikenessMissing
  = MaybeProjection
    -- ^ Projection-likeness analysis has not run on this function yet.
    -- It may do so in the future.
  | NeverProjection
    -- ^ The user has requested that this function be not be marked
    -- projection-like. The analysis may already have run on this
    -- function, but the results have been discarded, and it will not be
    -- run again.
  deriving (Show, Generic, Enum, Bounded)

data FunctionData = FunctionData
  { _funClauses        :: [Clause]
  , _funCompiled       :: Maybe CompiledClauses
      -- ^ 'Nothing' while function is still type-checked.
      --   @Just cc@ after type and coverage checking and
      --   translation to case trees.
  , _funSplitTree      :: Maybe SplitTree
      -- ^ The split tree constructed by the coverage
      --   checker. Needed to re-compile the clauses after
      --   forcing translation.
  , _funTreeless       :: Maybe Compiled
      -- ^ Intermediate representation for compiler backends.
  , _funCovering       :: [Clause]
      -- ^ Covering clauses computed by coverage checking.
      --   Erased by (IApply) confluence checking(?)
  , _funInv            :: FunctionInverse
  , _funMutual         :: Maybe [QName]
      -- ^ Mutually recursive functions, @data@s and @record@s.
      --   Does include this function.
      --   Empty list if not recursive.
      --   @Nothing@ if not yet computed (by positivity checker).
  , _funAbstr          :: IsAbstract
  , _funProjection     :: Either ProjectionLikenessMissing Projection
      -- ^ Is it a record projection?
      --   If yes, then return the name of the record type and index of
      --   the record argument.  Start counting with 1, because 0 means that
      --   it is already applied to the record. (Can happen in module
      --   instantiation.) This information is used in the termination
      --   checker.
  , _funErasure :: !Bool
    -- ^ Was @--erasure@ in effect when the function was defined?
    -- (This can affect the type of a projection.)
  , _funFlags          :: Set FunctionFlag
  , _funTerminates     :: Maybe Bool
      -- ^ Has this function been termination checked?  Did it pass?
  , _funExtLam         :: Maybe ExtLamInfo
      -- ^ Is this function generated from an extended lambda?
      --   If yes, then return the number of hidden and non-hidden lambda-lifted arguments.
  , _funWith           :: Maybe QName
      -- ^ Is this a generated with-function?
      --   If yes, then what's the name of the parent function?
  , _funIsKanOp        :: Maybe QName
      -- ^ Is this a helper for one of the Kan operations (transp,
      -- hcomp) on data types/records? If so, for which data type?
  , _funOpaque         :: IsOpaque
      -- ^ Is this function opaque? If so, and we're not in an opaque
      -- block that includes this function('s name), it will be treated
      -- abstractly.
  } deriving (Show, Generic)

pattern Function
  :: [Clause]
  -> Maybe CompiledClauses
  -> Maybe SplitTree
  -> Maybe Compiled
  -> [Clause]
  -> FunctionInverse
  -> Maybe [QName]
  -> IsAbstract
  -> Either ProjectionLikenessMissing Projection
  -> Bool
  -> Set FunctionFlag
  -> Maybe Bool
  -> Maybe ExtLamInfo
  -> Maybe QName
  -> Maybe QName
  -> IsOpaque
  -> Defn
pattern Function
  { funClauses
  , funCompiled
  , funSplitTree
  , funTreeless
  , funCovering
  , funInv
  , funMutual
  , funAbstr
  , funProjection
  , funErasure
  , funFlags
  , funTerminates
  , funExtLam
  , funWith
  , funIsKanOp
  , funOpaque
  } = FunctionDefn (FunctionData
    funClauses
    funCompiled
    funSplitTree
    funTreeless
    funCovering
    funInv
    funMutual
    funAbstr
    funProjection
    funErasure
    funFlags
    funTerminates
    funExtLam
    funWith
    funIsKanOp
    funOpaque
  )

data DatatypeData = DatatypeData
  { _dataPars           :: Nat
      -- ^ Number of parameters.
  , _dataIxs            :: Nat
      -- ^ Number of indices.
  , _dataClause         :: Maybe Clause
      -- ^ This might be in an instantiated module.
  , _dataCons           :: [QName]
      -- ^ Constructor names, ordered according to the order of their definition.
  , _dataSort           :: Sort
  , _dataMutual         :: Maybe [QName]
      -- ^ Mutually recursive functions, @data@s and @record@s.
      --   Does include this data type.
      --   Empty if not recursive.
      --   @Nothing@ if not yet computed (by positivity checker).
  , _dataAbstr          :: IsAbstract
  , _dataPathCons       :: [QName]
      -- ^ Path constructor names (subset of @dataCons@).
  , _dataTranspIx       :: Maybe QName
      -- ^ If indexed datatype, name of the "index transport" function.
  , _dataTransp         :: Maybe QName
      -- ^ Transport function, should be available for all datatypes in supported sorts.
  } deriving (Show, Generic)

pattern Datatype
  :: Nat
  -> Nat
  -> (Maybe Clause)
  -> [QName]
  -> Sort
  -> Maybe [QName]
  -> IsAbstract
  -> [QName]
  -> Maybe QName
  -> Maybe QName
  -> Defn

pattern Datatype
  { dataPars
  , dataIxs
  , dataClause
  , dataCons
  , dataSort
  , dataMutual
  , dataAbstr
  , dataPathCons
  , dataTranspIx
  , dataTransp
  } = DatatypeDefn (DatatypeData
    dataPars
    dataIxs
    dataClause
    dataCons
    dataSort
    dataMutual
    dataAbstr
    dataPathCons
    dataTranspIx
    dataTransp
  )

data RecordData = RecordData
  { _recPars           :: Nat
      -- ^ Number of parameters.
  , _recClause         :: Maybe Clause
      -- ^ Was this record type created by a module application?
      --   If yes, the clause is its definition (linking back to the original record type).
  , _recConHead        :: ConHead
      -- ^ Constructor name and fields.
  , _recNamedCon       :: Bool
      -- ^ Does this record have a @constructor@?
  , _recFields         :: [Dom QName]
      -- ^ The record field names.
  , _recTel            :: Telescope
      -- ^ The record field telescope. (Includes record parameters.)
      --   Note: @TelV recTel _ == telView' recConType@.
      --   Thus, @recTel@ is redundant.
  , _recMutual         :: Maybe [QName]
      -- ^ Mutually recursive functions, @data@s and @record@s.
      --   Does include this record.
      --   Empty if not recursive.
      --   @Nothing@ if not yet computed (by positivity checker).
  , _recEtaEquality'    :: EtaEquality
      -- ^ Eta-expand at this record type?
      --   @False@ for unguarded recursive records and coinductive records
      --   unless the user specifies otherwise.
  , _recPatternMatching :: PatternOrCopattern
      -- ^ In case eta-equality is off, do we allow pattern matching on the
      --   constructor or construction by copattern matching?
      --   Having both loses subject reduction, see issue #4560.
      --   After positivity checking, this field is obsolete, part of 'EtaEquality'.
  , _recInduction      :: Maybe Induction
      -- ^ 'Inductive' or 'CoInductive'?  Matters only for recursive records.
      --   'Nothing' means that the user did not specify it, which is an error
      --   for recursive records.
  , _recTerminates     :: Maybe Bool
      -- ^ 'Just True' means that unfolding of the recursive record terminates,
      --   'Just False' means that we have no evidence for termination,
      --   and 'Nothing' means we have not run the termination checker yet.
  , _recAbstr          :: IsAbstract
  , _recComp           :: CompKit
  } deriving (Show, Generic)

pattern Record
  :: Nat
  -> Maybe Clause
  -> ConHead
  -> Bool
  -> [Dom QName]
  -> Telescope
  -> Maybe [QName]
  -> EtaEquality
  -> PatternOrCopattern
  -> Maybe Induction
  -> Maybe Bool
  -> IsAbstract
  -> CompKit
  -> Defn

pattern Record
  { recPars
  , recClause
  , recConHead
  , recNamedCon
  , recFields
  , recTel
  , recMutual
  , recEtaEquality'
  , recPatternMatching
  , recInduction
  , recTerminates
  , recAbstr
  , recComp
  } = RecordDefn (RecordData
    recPars
    recClause
    recConHead
    recNamedCon
    recFields
    recTel
    recMutual
    recEtaEquality'
    recPatternMatching
    recInduction
    recTerminates
    recAbstr
    recComp
  )

data ConstructorData = ConstructorData
  { _conPars   :: Int
      -- ^ Number of parameters.
  , _conArity  :: Int
      -- ^ Number of arguments (excluding parameters).
  , _conSrcCon :: ConHead
      -- ^ Name of (original) constructor and fields. (This might be in a module instance.)
  , _conData   :: QName
      -- ^ Name of datatype or record type.
  , _conAbstr  :: IsAbstract
  , _conComp   :: CompKit
      -- ^ Cubical composition.
  , _conProj   :: Maybe [QName]
      -- ^ Projections. 'Nothing' if not yet computed.
  , _conForced :: [IsForced]
      -- ^ Which arguments are forced (i.e. determined by the type of the constructor)?
      --   Either this list is empty (if the forcing analysis isn't run), or its length is @conArity@.
  , _conErased :: Maybe [Bool]
      -- ^ Which arguments are erased at runtime (computed during compilation to treeless)?
      --   'True' means erased, 'False' means retained.
      --   'Nothing' if no erasure analysis has been performed yet.
      --   The length of the list is @conArity@.
  , _conErasure :: !Bool
      -- ^ Was @--erasure@ in effect when the constructor was defined?
      --   (This can affect the constructor's type.)
  , _conInline :: !Bool
      -- ^ Shall we translate the constructor on the root of the rhs into copattern matching on the lhs?
      --   Activated by INLINE pragma.
  } deriving (Show, Generic)

pattern Constructor
  :: Int
  -> Int
  -> ConHead
  -> QName
  -> IsAbstract
  -> CompKit
  -> Maybe [QName]
  -> [IsForced]
  -> Maybe [Bool]
  -> Bool
  -> Bool
  -> Defn
pattern Constructor
  { conPars
  , conArity
  , conSrcCon
  , conData
  , conAbstr
  , conComp
  , conProj
  , conForced
  , conErased
  , conErasure
  , conInline
  } = ConstructorDefn (ConstructorData
    conPars
    conArity
    conSrcCon
    conData
    conAbstr
    conComp
    conProj
    conForced
    conErased
    conErasure
    conInline
  )

data PrimitiveData = PrimitiveData
  { _primAbstr    :: IsAbstract
  , _primName     :: PrimitiveId
  , _primClauses  :: [Clause]
      -- ^ 'null' for primitive functions, @not null@ for builtin functions.
  , _primInv      :: FunctionInverse
      -- ^ Builtin functions can have inverses. For instance, natural number addition.
  , _primCompiled :: Maybe CompiledClauses
      -- ^ 'Nothing' for primitive functions,
      --   @'Just' something@ for builtin functions.
  , _primOpaque   :: IsOpaque
      -- ^ Primitives can also live in opaque blocks.
  } deriving (Show, Generic)

pattern Primitive
  :: IsAbstract
  -> PrimitiveId
  -> [Clause]
  -> FunctionInverse
  -> Maybe CompiledClauses
  -> IsOpaque
  -> Defn
pattern Primitive
  { primAbstr
  , primName
  , primClauses
  , primInv
  , primCompiled
  , primOpaque
  } = PrimitiveDefn (PrimitiveData
    primAbstr
    primName
    primClauses
    primInv
    primCompiled
    primOpaque
  )

data PrimitiveSortData = PrimitiveSortData
  { _primSortName :: BuiltinSort
  , _primSortSort :: Sort
  } deriving (Show, Generic)

pattern PrimitiveSort
  :: BuiltinSort
  -> Sort
  -> Defn
pattern PrimitiveSort
  { primSortName
  , primSortSort
  } = PrimitiveSortDefn (PrimitiveSortData
    primSortName
    primSortSort
  )

-- TODO: lenses for all Defn variants

lensFunction :: Lens' Defn FunctionData
lensFunction f = \case
  FunctionDefn d -> FunctionDefn <$> f d
  _ -> __IMPOSSIBLE__

lensConstructor :: Lens' Defn ConstructorData
lensConstructor f = \case
  ConstructorDefn d -> ConstructorDefn <$> f d
  _ -> __IMPOSSIBLE__

lensRecord :: Lens' Defn RecordData
lensRecord f = \case
  RecordDefn d -> RecordDefn <$> f d
  _ -> __IMPOSSIBLE__

-- Lenses for Record

lensRecTel :: Lens' RecordData Telescope
lensRecTel f r =
  f (_recTel r) <&> \ tel -> r { _recTel = tel }

-- Pretty printing definitions

instance Pretty Definition where
  pretty Defn{..} =
    "Defn {" <?> vcat
      [ "defArgInfo        =" <?> pshow defArgInfo
      , "defName           =" <?> pretty defName
      , "defType           =" <?> pretty defType
      , "defPolarity       =" <?> pshow defPolarity
      , "defArgOccurrences =" <?> pshow defArgOccurrences
      , "defGeneralizedParams =" <?> pshow defGeneralizedParams
      , "defDisplay        =" <?> pretty defDisplay
      , "defMutual         =" <?> pshow defMutual
      , "defCompiledRep    =" <?> pshow defCompiledRep
      , "defInstance       =" <?> pshow defInstance
      , "defCopy           =" <?> pshow defCopy
      , "defMatchable      =" <?> pshow (Set.toList defMatchable)
      , "defInjective      =" <?> pshow defInjective
      , "defCopatternLHS   =" <?> pshow defCopatternLHS
      , "theDef            =" <?> pretty theDef ] <+> "}"

instance Pretty Defn where
  pretty = \case
    AxiomDefn _         -> "Axiom"
    DataOrRecSigDefn d  -> pretty d
    GeneralizableVar    -> "GeneralizableVar"
    AbstractDefn def    -> "AbstractDefn" <?> parens (pretty def)
    FunctionDefn d      -> pretty d
    DatatypeDefn d      -> pretty d
    RecordDefn d        -> pretty d
    ConstructorDefn d   -> pretty d
    PrimitiveDefn d     -> pretty d
    PrimitiveSortDefn d -> pretty d

instance Pretty DataOrRecSigData where
  pretty (DataOrRecSigData n) = "DataOrRecSig" <+> pretty n

instance Pretty ProjectionLikenessMissing where
  pretty MaybeProjection = "MaybeProjection"
  pretty NeverProjection = "NeverProjection"

instance Pretty FunctionData where
  pretty (FunctionData
      funClauses
      funCompiled
      funSplitTree
      funTreeless
      _funCovering
      funInv
      funMutual
      funAbstr
      funProjection
      funErasure
      funFlags
      funTerminates
      _funExtLam
      funWith
      funIsKanOp
      funOpaque
    ) =
    "Function {" <?> vcat
      [ "funClauses      =" <?> vcat (map pretty funClauses)
      , "funCompiled     =" <?> pretty funCompiled
      , "funSplitTree    =" <?> pretty funSplitTree
      , "funTreeless     =" <?> pretty funTreeless
      , "funInv          =" <?> pretty funInv
      , "funMutual       =" <?> pshow funMutual
      , "funAbstr        =" <?> pshow funAbstr
      , "funProjection   =" <?> pretty funProjection
      , "funErasure      =" <?> pretty funErasure
      , "funFlags        =" <?> pshow funFlags
      , "funTerminates   =" <?> pshow funTerminates
      , "funWith         =" <?> pretty funWith
      , "funIsKanOp      =" <?> pretty funIsKanOp
      , "funOpaque       =" <?> pshow funOpaque
      ] <?> "}"

instance Pretty DatatypeData where
  pretty (DatatypeData
      dataPars
      dataIxs
      dataClause
      dataCons
      dataSort
      dataMutual
      _dataAbstr
      _dataPathCons
      _dataTranspIx
      _dataTransp
    ) =
    "Datatype {" <?> vcat
      [ "dataPars       =" <?> pshow dataPars
      , "dataIxs        =" <?> pshow dataIxs
      , "dataClause     =" <?> pretty dataClause
      , "dataCons       =" <?> pshow dataCons
      , "dataSort       =" <?> pretty dataSort
      , "dataMutual     =" <?> pshow dataMutual
      , "dataAbstr      =" <?> pshow dataAbstr
      ] <?> "}"

instance Pretty RecordData where
  pretty (RecordData
      recPars
      recClause
      recConHead
      recNamedCon
      recFields
      recTel
      recMutual
      recEtaEquality'
      _recPatternMatching
      recInduction
      _recTerminates
      recAbstr
      _recComp
    ) =
    "Record {" <?> vcat
      [ "recPars         =" <?> pshow recPars
      , "recClause       =" <?> pretty recClause
      , "recConHead      =" <?> pretty recConHead
      , "recNamedCon     =" <?> pretty recNamedCon
      , "recFields       =" <?> pretty recFields
      , "recTel          =" <?> pretty recTel
      , "recMutual       =" <?> pshow recMutual
      , "recEtaEquality' =" <?> pshow recEtaEquality'
      , "recInduction    =" <?> pshow recInduction
      , "recAbstr        =" <?> pshow recAbstr
      ] <?> "}"

instance Pretty ConstructorData where
  pretty (ConstructorData
      conPars
      conArity
      conSrcCon
      conData
      conAbstr
      _conComp
      _conProj
      _conForced
      conErased
      conErasure
      conInline
    ) =
    "Constructor {" <?> vcat
      [ "conPars    =" <?> pshow conPars
      , "conArity   =" <?> pshow conArity
      , "conSrcCon  =" <?> pretty conSrcCon
      , "conData    =" <?> pretty conData
      , "conAbstr   =" <?> pshow conAbstr
      , "conErased  =" <?> pshow conErased
      , "conErasure =" <?> pshow conErasure
      , "conInline  =" <?> pshow conInline
      ] <?> "}"

instance Pretty PrimitiveData where
  pretty (PrimitiveData
      primAbstr
      primName
      primClauses
      _primInv
      primCompiled
      primOpaque
      ) =
    "Primitive {" <?> vcat
      [ "primAbstr    =" <?> pshow primAbstr
      , "primName     =" <?> pshow primName
      , "primClauses  =" <?> pshow primClauses
      , "primCompiled =" <?> pshow primCompiled
      , "primOpaque   =" <?> pshow primOpaque
      ] <?> "}"

instance Pretty PrimitiveSortData where
  pretty (PrimitiveSortData primSortName primSortSort) =
    "PrimitiveSort {" <?> vcat
      [ "primSortName =" <?> pshow primSortName
      , "primSortSort =" <?> pshow primSortSort
      ] <?> "}"

instance Pretty Projection where
  pretty Projection{..} =
    "Projection {" <?> vcat
      [ "projProper   =" <?> pretty projProper
      , "projOrig     =" <?> pretty projOrig
      , "projFromType =" <?> pretty projFromType
      , "projIndex    =" <?> pshow projIndex
      , "projLams     =" <?> pretty projLams
      ]

instance Pretty c => Pretty (FunctionInverse' c) where
  pretty NotInjective = "NotInjective"
  pretty (Inverse inv) = "Inverse" <?>
    vcat [ pretty h <+> "->" <?> pretty cs
         | (h, cs) <- Map.toList inv ]

instance Pretty ProjLams where
  pretty (ProjLams args) = pretty args

-- | Is the record type recursive?
recRecursive :: Defn -> Bool
recRecursive (Record { recMutual = Just qs }) = not $ null qs
recRecursive _ = __IMPOSSIBLE__

recEtaEquality :: Defn -> HasEta
recEtaEquality = theEtaEquality . recEtaEquality'

-- | A template for creating 'Function' definitions, with sensible
-- defaults.
emptyFunctionData :: HasOptions m => m FunctionData
emptyFunctionData = do
  erasure <- optErasure <$> pragmaOptions
  return $ FunctionData
    { _funClauses     = []
    , _funCompiled    = Nothing
    , _funSplitTree   = Nothing
    , _funTreeless    = Nothing
    , _funInv         = NotInjective
    , _funMutual      = Nothing
    , _funAbstr       = ConcreteDef
    , _funProjection  = Left MaybeProjection
    , _funErasure     = erasure
    , _funFlags       = Set.empty
    , _funTerminates  = Nothing
    , _funExtLam      = Nothing
    , _funWith        = Nothing
    , _funCovering    = []
    , _funIsKanOp     = Nothing
    , _funOpaque      = TransparentDef
    }

emptyFunction :: HasOptions m => m Defn
emptyFunction = FunctionDefn <$> emptyFunctionData

funFlag :: FunctionFlag -> Lens' Defn Bool
funFlag flag f def@Function{ funFlags = flags } =
  f (Set.member flag flags) <&>
  \ b -> def{ funFlags = (if b then Set.insert else Set.delete) flag flags }
funFlag _ f def = f False $> def

funStatic, funInline, funMacro :: Lens' Defn Bool
funStatic       = funFlag FunStatic
funInline       = funFlag FunInline
funMacro        = funFlag FunMacro

isMacro :: Defn -> Bool
isMacro = (^. funMacro)

-- | Checking whether we are dealing with a function yet to be defined.
isEmptyFunction :: Defn -> Bool
isEmptyFunction def =
  case def of
    Function { funClauses = [] } -> True
    _ -> False

isCopatternLHS :: [Clause] -> Bool
isCopatternLHS = List.any (List.any (isJust . A.isProjP) . namedClausePats)

recCon :: Defn -> QName
recCon Record{ recConHead } = conName recConHead
recCon _ = __IMPOSSIBLE__

defIsRecord :: Defn -> Bool
defIsRecord Record{} = True
defIsRecord _        = False

defIsDataOrRecord :: Defn -> Bool
defIsDataOrRecord Record{}   = True
defIsDataOrRecord Datatype{} = True
defIsDataOrRecord _          = False

defConstructors :: Defn -> [QName]
defConstructors Datatype{dataCons = cs} = cs
defConstructors Record{recConHead = c} = [conName c]
defConstructors _ = __IMPOSSIBLE__

newtype Fields = Fields [(C.Name, Type)]
  deriving Null

-- | Did we encounter a simplifying reduction?
--   In terms of CIC, that would be a iota-reduction.
--   In terms of Agda, this is a constructor or literal
--   pattern that matched.
--   Just beta-reduction (substitution) or delta-reduction
--   (unfolding of definitions) does not count as simplifying?

data Simplification = YesSimplification | NoSimplification
  deriving (Eq, Show, Generic)

instance Null Simplification where
  empty = NoSimplification
  null  = (== NoSimplification)

instance Semigroup Simplification where
  YesSimplification <> _ = YesSimplification
  NoSimplification  <> s = s

instance Monoid Simplification where
  mempty = NoSimplification
  mappend = (<>)

data Reduced no yes
  = NoReduction no
  | YesReduction Simplification yes
  deriving Functor

redReturn :: a -> ReduceM (Reduced a' a)
redReturn = return . YesReduction YesSimplification

-- | Conceptually: @redBind m f k = either (return . Left . f) k =<< m@

redBind :: ReduceM (Reduced a a') -> (a -> b) ->
           (a' -> ReduceM (Reduced b b')) -> ReduceM (Reduced b b')
redBind ma f k = do
  r <- ma
  case r of
    NoReduction x    -> return $ NoReduction $ f x
    YesReduction _ y -> k y

-- | Three cases: 1. not reduced, 2. reduced, but blocked, 3. reduced, not blocked.
data IsReduced
  = NotReduced
  | Reduced    (Blocked ())

data MaybeReduced a = MaybeRed
  { isReduced     :: IsReduced
  , ignoreReduced :: a
  }
  deriving (Functor)

instance IsProjElim e => IsProjElim (MaybeReduced e) where
  isProjElim = isProjElim . ignoreReduced

type MaybeReducedArgs = [MaybeReduced (Arg Term)]
type MaybeReducedElims = [MaybeReduced Elim]

notReduced :: a -> MaybeReduced a
notReduced x = MaybeRed NotReduced x

reduced :: Blocked (Arg Term) -> MaybeReduced (Arg Term)
reduced b = MaybeRed (Reduced $ () <$ b) $ ignoreBlocking b

-- | Controlling 'reduce'.
data AllowedReduction
  = ProjectionReductions     -- ^ (Projection and) projection-like functions may be reduced.
  | InlineReductions         -- ^ Functions marked INLINE may be reduced.
  | CopatternReductions      -- ^ Copattern definitions may be reduced.
  | FunctionReductions       -- ^ Non-recursive functions and primitives may be reduced.
  | RecursiveReductions      -- ^ Even recursive functions may be reduced.
  | LevelReductions          -- ^ Reduce @'Level'@ terms.
  | TypeLevelReductions      -- ^ Allow @allReductions@ in types, even
                             --   if not allowed at term level (used
                             --   by confluence checker)
  | UnconfirmedReductions    -- ^ Functions whose termination has not (yet) been confirmed.
  | NonTerminatingReductions -- ^ Functions that have failed termination checking.
  deriving (Show, Eq, Ord, Enum, Bounded, Ix, Generic)

instance SmallSet.SmallSetElement AllowedReduction

type AllowedReductions = SmallSet AllowedReduction

-- | Not quite all reductions (skip non-terminating reductions)
allReductions :: AllowedReductions
allReductions = SmallSet.delete NonTerminatingReductions reallyAllReductions

reallyAllReductions :: AllowedReductions
reallyAllReductions = SmallSet.total

data ReduceDefs
  = OnlyReduceDefs (Set QName)
  | DontReduceDefs (Set QName)
  deriving Generic

reduceAllDefs :: ReduceDefs
reduceAllDefs = DontReduceDefs empty

locallyReduceDefs :: MonadTCEnv m => ReduceDefs -> m a -> m a
locallyReduceDefs = locallyTC eReduceDefs . const

locallyReduceAllDefs :: MonadTCEnv m => m a -> m a
locallyReduceAllDefs = locallyReduceDefs reduceAllDefs

shouldReduceDef :: (MonadTCEnv m) => QName -> m Bool
shouldReduceDef f = asksTC envReduceDefs <&> \case
  OnlyReduceDefs defs -> f `Set.member` defs
  DontReduceDefs defs -> not $ f `Set.member` defs

toReduceDefs :: (Bool, [QName]) -> ReduceDefs
toReduceDefs (True,  ns) = OnlyReduceDefs (Data.Set.fromList ns)
toReduceDefs (False, ns) = DontReduceDefs (Data.Set.fromList ns)

fromReduceDefs :: ReduceDefs -> (Bool, [QName])
fromReduceDefs (OnlyReduceDefs ns) = (True,  toList ns)
fromReduceDefs (DontReduceDefs ns) = (False, toList ns)

locallyReconstructed :: MonadTCEnv m => m a -> m a
locallyReconstructed = locallyTC eReconstructed . const $ True

isReconstructed :: (MonadTCEnv m) => m Bool
isReconstructed = asksTC envReconstructed

-- | Primitives

data PrimitiveImpl = PrimImpl Type PrimFun

data PrimFun = PrimFun
  { primFunName           :: QName
  , primFunArity          :: Arity
  , primFunArgOccurrences :: [Occurrence]
    -- ^ See 'defArgOccurrences'.
  , primFunImplementation :: [Arg Term] -> Int -> ReduceM (Reduced MaybeReducedArgs Term)
  }
  deriving Generic

primFun :: QName -> Arity -> ([Arg Term] -> ReduceM (Reduced MaybeReducedArgs Term)) -> PrimFun
primFun q ar imp = PrimFun q ar [] (\args _ -> imp args)

defClauses :: Definition -> [Clause]
defClauses Defn{theDef = Function{funClauses = cs}}        = cs
defClauses Defn{theDef = Primitive{primClauses = cs}}      = cs
defClauses Defn{theDef = Datatype{dataClause = Just c}}    = [c]
defClauses Defn{theDef = Record{recClause = Just c}}       = [c]
defClauses _                                               = []

defCompiled :: Definition -> Maybe CompiledClauses
defCompiled Defn{theDef = Function {funCompiled  = mcc}} = mcc
defCompiled Defn{theDef = Primitive{primCompiled = mcc}} = mcc
defCompiled _ = Nothing

defParameters :: Definition -> Maybe Nat
defParameters Defn{theDef = Datatype{dataPars = n}} = Just n
defParameters Defn{theDef = Record  {recPars  = n}} = Just n
defParameters _                                     = Nothing

defInverse :: Definition -> FunctionInverse
defInverse Defn{theDef = Function { funInv  = inv }} = inv
defInverse Defn{theDef = Primitive{ primInv = inv }} = inv
defInverse _                                         = NotInjective

defCompilerPragmas :: BackendName -> Definition -> [CompilerPragma]
defCompilerPragmas b = reverse . fromMaybe [] . Map.lookup b . defCompiledRep
  -- reversed because we add new pragmas to the front of the list

-- | Has the definition failed the termination checker?
defNonterminating :: Definition -> Bool
defNonterminating Defn{theDef = Function{funTerminates = Just False}} = True
defNonterminating _                                                   = False

-- | Has the definition not termination checked or did the check fail?
defTerminationUnconfirmed :: Definition -> Bool
defTerminationUnconfirmed Defn{theDef = Function{funTerminates = Just True}} = False
defTerminationUnconfirmed Defn{theDef = Function{funTerminates = _        }} = True
defTerminationUnconfirmed _ = False

defAbstract :: Definition -> IsAbstract
defAbstract d = case theDef d of
    Axiom{}                   -> ConcreteDef
    DataOrRecSig{}            -> ConcreteDef
    GeneralizableVar{}        -> ConcreteDef
    AbstractDefn{}            -> AbstractDef
    Function{funAbstr = a}    -> a
    Datatype{dataAbstr = a}   -> a
    Record{recAbstr = a}      -> a
    Constructor{conAbstr = a} -> a
    Primitive{primAbstr = a}  -> a
    PrimitiveSort{}           -> ConcreteDef

defOpaque :: Definition -> IsOpaque
defOpaque d = case theDef d of
    -- These two can be opaque:
    Function{funOpaque=o}     -> o
    Primitive{primOpaque=o}   -> o

    -- Doesn't matter whether or not it's opaque:
    Axiom{}                   -> TransparentDef
    -- Concreteness is orthogonal to opacity:
    AbstractDefn{}            -> TransparentDef

    -- None of these are supported in opaque blocks:
    DataOrRecSig{}            -> TransparentDef
    GeneralizableVar{}        -> TransparentDef
    Datatype{}                -> TransparentDef
    Record{}                  -> TransparentDef
    Constructor{}             -> TransparentDef
    PrimitiveSort{}           -> TransparentDef

defForced :: Definition -> [IsForced]
defForced d = case theDef d of
    Constructor{conForced = fs} -> fs
    Axiom{}                     -> []
    DataOrRecSig{}              -> []
    GeneralizableVar{}          -> []
    AbstractDefn{}              -> []
    Function{}                  -> []
    Datatype{}                  -> []
    Record{}                    -> []
    Primitive{}                 -> []
    PrimitiveSort{}             -> []

---------------------------------------------------------------------------
-- ** Injectivity
---------------------------------------------------------------------------

type FunctionInverse = FunctionInverse' Clause
type InversionMap c = Map TermHead [c]

data FunctionInverse' c
  = NotInjective
  | Inverse (InversionMap c)
  deriving (Show, Functor, Generic)

data TermHead = SortHead
              | PiHead
              | ConsHead QName
              | VarHead Nat
              | UnknownHead
  deriving (Eq, Ord, Show, Generic)

instance Pretty TermHead where
  pretty = \ case
    SortHead    -> "SortHead"
    PiHead      -> "PiHead"
    ConsHead q  -> "ConsHead" <+> pretty q
    VarHead i   -> text ("VarHead " ++ show i)
    UnknownHead -> "UnknownHead"

---------------------------------------------------------------------------
-- ** Mutual blocks
---------------------------------------------------------------------------

newtype MutualId = MutId Int32
  deriving (Eq, Ord, Show, Num, Enum, NFData)

---------------------------------------------------------------------------
-- ** Statistics
---------------------------------------------------------------------------

type Statistics = Map String Integer

---------------------------------------------------------------------------
-- ** Trace
---------------------------------------------------------------------------

data Call
  = CheckClause Type A.SpineClause
  | CheckLHS A.SpineLHS
  | CheckPattern A.Pattern Telescope Type
  | CheckPatternLinearityType C.Name
  | CheckPatternLinearityValue C.Name
  | CheckLetBinding A.LetBinding
  | InferExpr A.Expr
  | CheckExprCall Comparison A.Expr Type
  | CheckDotPattern A.Expr Term
  | CheckProjection Range QName Type
  | IsTypeCall Comparison A.Expr Sort
  | IsType_ A.Expr
  | InferVar Name
  | InferDef QName
  | CheckArguments Range [NamedArg A.Expr] Type (Maybe Type)
  | CheckMetaSolution Range MetaId Type Term
  | CheckTargetType Range Type Type
  | CheckDataDef Range QName [A.LamBinding] [A.Constructor]
  | CheckRecDef Range QName [A.LamBinding] [A.Constructor]
  | CheckConstructor QName Telescope Sort A.Constructor
  | CheckConArgFitsIn QName Bool Type Sort
  | CheckFunDefCall Range QName [A.Clause] Bool
    -- ^ Highlight (interactively) if and only if the boolean is 'True'.
  | CheckPragma Range A.Pragma
  | CheckPrimitive Range QName A.Expr
  | CheckIsEmpty Range Type
  | CheckConfluence QName QName
  | CheckModuleParameters ModuleName A.Telescope
  | CheckWithFunctionType Type
  | CheckSectionApplication Range Erased ModuleName A.ModuleApplication
  | CheckNamedWhere ModuleName
  -- | Checking a clause for confluence with endpoint reductions. Always
  -- @φ ⊢ f vs = rhs@ for now, but we store the simplifications of
    -- @f vs[φ]@ and @rhs[φ]@.
  | CheckIApplyConfluence
      Range  -- ^ Clause range
      QName  -- ^ Function name
      Term   -- ^ (As-is) Function applied to the patterns in this clause
      Term   -- ^ (Simplified) Function applied to the patterns in this clause
      Term   -- ^ (Simplified) clause RHS
      Type   -- ^ (Simplified) clause type
  | ScopeCheckExpr C.Expr
  | ScopeCheckDeclaration NiceDeclaration
  | ScopeCheckLHS C.QName C.Pattern
  | NoHighlighting
  | ModuleContents  -- ^ Interaction command: show module contents.
  | SetRange Range  -- ^ used by 'setCurrentRange'
  deriving Generic

instance Pretty Call where
    pretty CheckClause{}             = "CheckClause"
    pretty CheckLHS{}                = "CheckLHS"
    pretty CheckPattern{}            = "CheckPattern"
    pretty CheckPatternLinearityType{}  = "CheckPatternLinearityType"
    pretty CheckPatternLinearityValue{} = "CheckPatternLinearityValue"
    pretty InferExpr{}               = "InferExpr"
    pretty CheckExprCall{}           = "CheckExprCall"
    pretty CheckLetBinding{}         = "CheckLetBinding"
    pretty CheckProjection{}         = "CheckProjection"
    pretty IsTypeCall{}              = "IsTypeCall"
    pretty IsType_{}                 = "IsType_"
    pretty InferVar{}                = "InferVar"
    pretty InferDef{}                = "InferDef"
    pretty CheckArguments{}          = "CheckArguments"
    pretty CheckMetaSolution{}       = "CheckMetaSolution"
    pretty CheckTargetType{}         = "CheckTargetType"
    pretty CheckDataDef{}            = "CheckDataDef"
    pretty CheckRecDef{}             = "CheckRecDef"
    pretty CheckConstructor{}        = "CheckConstructor"
    pretty CheckConArgFitsIn{}       = "CheckConArgFitsIn"
    pretty CheckFunDefCall{}         = "CheckFunDefCall"
    pretty CheckPragma{}             = "CheckPragma"
    pretty CheckPrimitive{}          = "CheckPrimitive"
    pretty CheckModuleParameters{}   = "CheckModuleParameters"
    pretty CheckWithFunctionType{}   = "CheckWithFunctionType"
    pretty CheckNamedWhere{}         = "CheckNamedWhere"
    pretty ScopeCheckExpr{}          = "ScopeCheckExpr"
    pretty ScopeCheckDeclaration{}   = "ScopeCheckDeclaration"
    pretty ScopeCheckLHS{}           = "ScopeCheckLHS"
    pretty CheckDotPattern{}         = "CheckDotPattern"
    pretty SetRange{}                = "SetRange"
    pretty CheckSectionApplication{} = "CheckSectionApplication"
    pretty CheckIsEmpty{}            = "CheckIsEmpty"
    pretty CheckConfluence{}         = "CheckConfluence"
    pretty NoHighlighting{}          = "NoHighlighting"
    pretty ModuleContents{}          = "ModuleContents"
    pretty CheckIApplyConfluence{}   = "ModuleContents"

instance HasRange Call where
    getRange (CheckClause _ c)                   = getRange c
    getRange (CheckLHS lhs)                      = getRange lhs
    getRange (CheckPattern p _ _)                = getRange p
    getRange (CheckPatternLinearityType x)       = getRange x
    getRange (CheckPatternLinearityValue x)      = getRange x
    getRange (InferExpr e)                       = getRange e
    getRange (CheckExprCall _ e _)               = getRange e
    getRange (CheckLetBinding b)                 = getRange b
    getRange (CheckProjection r _ _)             = r
    getRange (IsTypeCall cmp e s)                = getRange e
    getRange (IsType_ e)                         = getRange e
    getRange (InferVar x)                        = getRange x
    getRange (InferDef f)                        = getRange f
    getRange (CheckArguments r _ _ _)            = r
    getRange (CheckMetaSolution r _ _ _)         = r
    getRange (CheckTargetType r _ _)             = r
    getRange (CheckDataDef i _ _ _)              = getRange i
    getRange (CheckRecDef i _ _ _)               = getRange i
    getRange (CheckConstructor _ _ _ c)          = getRange c
    getRange (CheckConArgFitsIn c _ _ _)         = getRange c
    getRange (CheckFunDefCall i _ _ _)           = getRange i
    getRange (CheckPragma r _)                   = r
    getRange (CheckPrimitive i _ _)              = getRange i
    getRange (CheckModuleParameters _ tel)       = getRange tel
    getRange CheckWithFunctionType{}             = noRange
    getRange (CheckNamedWhere m)                 = getRange m
    getRange (ScopeCheckExpr e)                  = getRange e
    getRange (ScopeCheckDeclaration d)           = getRange d
    getRange (ScopeCheckLHS _ p)                 = getRange p
    getRange (CheckDotPattern e _)               = getRange e
    getRange (SetRange r)                        = r
    getRange (CheckSectionApplication r _ _ _)   = r
    getRange (CheckIsEmpty r _)                  = r
    getRange (CheckConfluence rule1 rule2)       = max (getRange rule1) (getRange rule2)
    getRange NoHighlighting                      = noRange
    getRange ModuleContents                      = noRange
    getRange (CheckIApplyConfluence e _ _ _ _ _) = getRange e

---------------------------------------------------------------------------
-- ** Instance table
---------------------------------------------------------------------------

-- | The instance table is a @Map@ associating to every name of
--   record/data type/postulate its list of instances
type InstanceTable = Map QName (Set QName)

-- | When typechecking something of the following form:
--
--     instance
--       x : _
--       x = y
--
--   it's not yet known where to add @x@, so we add it to a list of
--   unresolved instances and we'll deal with it later.
type TempInstanceTable = (InstanceTable , Set QName)

---------------------------------------------------------------------------
-- ** Builtin things
---------------------------------------------------------------------------

data BuiltinSort
  = SortUniv Univ
  | SortOmega Univ
  | SortIntervalUniv
  | SortLevelUniv
  deriving (Show, Eq, Generic)

pattern SortProp, SortSet, SortStrictSet, SortPropOmega, SortSetOmega, SortStrictSetOmega :: BuiltinSort
pattern SortProp           = SortUniv  UProp
pattern SortSet            = SortUniv  UType
pattern SortStrictSet      = SortUniv  USSet
pattern SortPropOmega      = SortOmega UProp
pattern SortSetOmega       = SortOmega UType
pattern SortStrictSetOmega = SortOmega USSet

{-# COMPLETE
  SortProp, SortSet, SortStrictSet,
  SortPropOmega, SortSetOmega, SortStrictSetOmega,
  SortIntervalUniv, SortLevelUniv #-}

data BuiltinDescriptor
  = BuiltinData (TCM Type) [BuiltinId]
  | BuiltinDataCons (TCM Type)
  | BuiltinPrim PrimitiveId (Term -> TCM ())
  | BuiltinSort BuiltinSort
  | BuiltinPostulate Relevance (TCM Type)
  | BuiltinUnknown (Maybe (TCM Type)) (Term -> Type -> TCM ())
    -- ^ Builtin of any kind.
    --   Type can be checked (@Just t@) or inferred (@Nothing@).
    --   The second argument is the hook for the verification function.

data BuiltinInfo =
   BuiltinInfo { builtinName :: BuiltinId
               , builtinDesc :: BuiltinDescriptor }

type BuiltinThings pf = Map SomeBuiltin (Builtin pf)

data Builtin pf
        = Builtin Term
        | Prim pf
        | BuiltinRewriteRelations (Set QName)
            -- ^ @BUILTIN REWRITE@.  We can have several rewrite relations.
    deriving (Show, Functor, Foldable, Traversable, Generic)

---------------------------------------------------------------------------
-- * Highlighting levels
---------------------------------------------------------------------------

-- | How much highlighting should be sent to the user interface?

data HighlightingLevel
  = None
  | NonInteractive
  | Interactive
    -- ^ This includes both non-interactive highlighting and
    -- interactive highlighting of the expression that is currently
    -- being type-checked.
    deriving (Eq, Ord, Show, Read, Generic)

-- | How should highlighting be sent to the user interface?

data HighlightingMethod
  = Direct
    -- ^ Via stdout.
  | Indirect
    -- ^ Both via files and via stdout.
    deriving (Eq, Show, Read, Generic)

-- | @ifTopLevelAndHighlightingLevelIs l b m@ runs @m@ when we're
-- type-checking the top-level module (or before we've started doing
-- this) and either the highlighting level is /at least/ @l@ or @b@ is
-- 'True'.

ifTopLevelAndHighlightingLevelIsOr ::
  MonadTCEnv tcm => HighlightingLevel -> Bool -> tcm () -> tcm ()
ifTopLevelAndHighlightingLevelIsOr l b m = do
  e <- askTC
  when (envHighlightingLevel e >= l || b) $
    case (envImportPath e) of
      -- Below the main module.
      (_:_:_) -> pure ()
      -- In or before the top-level module.
      _ -> m

-- | @ifTopLevelAndHighlightingLevelIs l m@ runs @m@ when we're
-- type-checking the top-level module (or before we've started doing
-- this) and the highlighting level is /at least/ @l@.

ifTopLevelAndHighlightingLevelIs ::
  MonadTCEnv tcm => HighlightingLevel -> tcm () -> tcm ()
ifTopLevelAndHighlightingLevelIs l =
  ifTopLevelAndHighlightingLevelIsOr l False

---------------------------------------------------------------------------
-- * Type checking environment
---------------------------------------------------------------------------

data TCEnv =
    TCEnv { envContext             :: Context
          , envLetBindings         :: LetBindings
          , envCurrentModule       :: ModuleName
          , envCurrentPath         :: Maybe AbsolutePath
            -- ^ The path to the file that is currently being
            -- type-checked.  'Nothing' if we do not have a file
            -- (like in interactive mode see @CommandLine@).
          , envAnonymousModules    :: [(ModuleName, Nat)] -- ^ anonymous modules and their number of free variables
          , envImportPath          :: [TopLevelModuleName]
            -- ^ The module stack with the entry being the top-level module as
            --   Agda chases modules. It will be empty if there is no main
            --   module, will have a single entry for the top level module, or
            --   more when descending past the main module. This is used to
            --   detect import cycles and in some cases highlighting behavior.
            --   The level of a given module is not necessarily the same as the
            --   length, in the module dependency graph, of the shortest path
            --   from the top-level module; it depends on in which order Agda
            --   chooses to chase dependencies.
          , envMutualBlock         :: Maybe MutualId -- ^ the current (if any) mutual block
          , envTerminationCheck    :: TerminationCheck ()  -- ^ are we inside the scope of a termination pragma
          , envCoverageCheck       :: CoverageCheck        -- ^ are we inside the scope of a coverage pragma
          , envMakeCase            :: Bool                 -- ^ are we inside a make-case (if so, ignore forcing analysis in unifier)
          , envSolvingConstraints  :: Bool
                -- ^ Are we currently in the process of solving active constraints?
          , envCheckingWhere       :: Bool
                -- ^ Have we stepped into the where-declarations of a clause?
                --   Everything under a @where@ will be checked with this flag on.
          , envWorkingOnTypes      :: Bool
                -- ^ Are we working on types? Turned on by 'workOnTypes'.
          , envAssignMetas         :: Bool
            -- ^ Are we allowed to assign metas?
          , envActiveProblems      :: Set ProblemId
          , envAbstractMode        :: AbstractMode
                -- ^ When checking the typesignature of a public definition
                --   or the body of a non-abstract definition this is true.
                --   To prevent information about abstract things leaking
                --   outside the module.
          , envRelevance           :: Relevance
                -- ^ Are we checking an irrelevant argument? (=@Irrelevant@)
                -- Then top-level irrelevant declarations are enabled.
                -- Other value: @Relevant@, then only relevant decls. are available.
          , envQuantity            :: Quantity
                -- ^ Are we checking a runtime-irrelevant thing? (='Quantity0')
                -- Then runtime-irrelevant things are usable.
          , envHardCompileTimeMode :: Bool
                -- ^ Is the \"hard\" compile-time mode enabled? In
                -- this mode the quantity component of the environment
                -- is always zero, and every new definition is treated
                -- as erased.
          , envSplitOnStrict       :: Bool
                -- ^ Are we currently case-splitting on a strict
                --   datatype (i.e. in SSet)? If yes, the
                --   pattern-matching unifier will solve reflexive
                --   equations even --without-K.
          , envDisplayFormsEnabled :: Bool
                -- ^ Sometimes we want to disable display forms.
          , envFoldLetBindings :: Bool
                -- ^ Fold let-bindings when printing terms (default: True)
          , envRange :: Range
          , envHighlightingRange :: Range
                -- ^ Interactive highlighting uses this range rather
                --   than 'envRange'.
          , envClause :: IPClause
                -- ^ What is the current clause we are type-checking?
                --   Will be recorded in interaction points in this clause.
          , envCall  :: Maybe (Closure Call)
                -- ^ what we're doing at the moment
          , envHighlightingLevel  :: HighlightingLevel
                -- ^ Set to 'None' when imported modules are
                --   type-checked.
          , envHighlightingMethod :: HighlightingMethod
          , envExpandLast :: ExpandHidden
                -- ^ When type-checking an alias f=e, we do not want
                -- to insert hidden arguments in the end, because
                -- these will become unsolved metas.
          , envAppDef :: Maybe QName
                -- ^ We are reducing an application of this function.
                -- (For tracking of incomplete matches.)
          , envSimplification :: Simplification
                -- ^ Did we encounter a simplification (proper match)
                --   during the current reduction process?
          , envAllowedReductions :: AllowedReductions
          , envReduceDefs :: ReduceDefs
          , envReconstructed :: Bool
          , envInjectivityDepth :: Int
                -- ^ Injectivity can cause non-termination for unsolvable contraints
                --   (#431, #3067). Keep a limit on the nesting depth of injectivity
                --   uses.
          , envCompareBlocked :: Bool
                -- ^ When @True@, the conversion checker will consider
                --   all term constructors as injective, including
                --   blocked function applications and metas. Warning:
                --   this should only be used when not assigning any
                --   metas (e.g. when @envAssignMetas@ is @False@ or
                --   when running @pureEqualTerms@) or else we get
                --   non-unique meta solutions.
          , envPrintDomainFreePi :: Bool
                -- ^ When @True@, types will be omitted from printed pi types if they
                --   can be inferred.
          , envPrintMetasBare :: Bool
                -- ^ When @True@, throw away meta numbers and meta elims.
                --   This is used for reifying terms for feeding into the
                --   user's source code, e.g., for the interaction tactics @solveAll@.
          , envInsideDotPattern :: Bool
                -- ^ Used by the scope checker to make sure that certain forms
                --   of expressions are not used inside dot patterns: extended
                --   lambdas and let-expressions.
          , envUnquoteFlags :: UnquoteFlags
          , envInstanceDepth :: !Int
                -- ^ Until we get a termination checker for instance search (#1743) we
                --   limit the search depth to ensure termination.
          , envIsDebugPrinting :: Bool
          , envPrintingPatternLambdas :: [QName]
                -- ^ #3004: pattern lambdas with copatterns may refer to themselves. We
                --   don't have a good story for what to do in this case, but at least
                --   printing shouldn't loop. Here we keep track of which pattern lambdas
                --   we are currently in the process of printing.
          , envCallByNeed :: Bool
                -- ^ Use call-by-need evaluation for reductions.
          , envCurrentCheckpoint :: CheckpointId
                -- ^ Checkpoints track the evolution of the context as we go
                -- under binders or refine it by pattern matching.
          , envCheckpoints :: Map CheckpointId Substitution
                -- ^ Keeps the substitution from each previous checkpoint to
                --   the current context.
          , envGeneralizeMetas :: DoGeneralize
                -- ^ Should new metas generalized over.
          , envGeneralizedVars :: Map QName GeneralizedValue
                -- ^ Values for used generalizable variables.
          , envActiveBackendName :: Maybe BackendName
                -- ^ Is some backend active at the moment, and if yes, which?
                --   NB: we only store the 'BackendName' here, otherwise
                --   @instance Data TCEnv@ is not derivable.
                --   The actual backend can be obtained from the name via 'stBackends'.
          , envConflComputingOverlap :: Bool
                -- ^ Are we currently computing the overlap between
                --   two rewrite rules for the purpose of confluence checking?
          , envCurrentlyElaborating :: Bool
                -- ^ Are we currently in the process of executing an
                --   elaborate-and-give interactive command?
          , envSyntacticEqualityFuel :: !(Strict.Maybe Int)
                -- ^ If this counter is 'Strict.Nothing', then
                -- syntactic equality checking is unrestricted. If it
                -- is zero, then syntactic equality checking is not
                -- run at all. If it is a positive number, then
                -- syntactic equality checking is allowed to run, but
                -- the counter is decreased in the failure
                -- continuation of
                -- 'Agda.TypeChecking.SyntacticEquality.checkSyntacticEquality'.
          , envCurrentOpaqueId :: !(Maybe OpaqueId)
                -- ^ Unique identifier of the opaque block we are
                -- currently under, if any. Used by the scope checker
                -- (to associate definitions to blocks), and by the type
                -- checker (for unfolding control).
          }
    deriving (Generic)

initEnv :: TCEnv
initEnv = TCEnv { envContext             = []
                , envLetBindings         = Map.empty
                , envCurrentModule       = noModuleName
                , envCurrentPath         = Nothing
                , envAnonymousModules    = []
                , envImportPath          = []
                , envMutualBlock         = Nothing
                , envTerminationCheck    = TerminationCheck
                , envCoverageCheck       = YesCoverageCheck
                , envMakeCase            = False
                , envSolvingConstraints  = False
                , envCheckingWhere       = False
                , envActiveProblems      = Set.empty
                , envWorkingOnTypes      = False
                , envAssignMetas         = True
                , envAbstractMode        = ConcreteMode
  -- Andreas, 2013-02-21:  This was 'AbstractMode' until now.
  -- However, top-level checks for mutual blocks, such as
  -- constructor-headedness, should not be able to look into
  -- abstract definitions unless abstract themselves.
  -- (See also discussion on issue 796.)
  -- The initial mode should be 'ConcreteMode', ensuring you
  -- can only look into abstract things in an abstract
  -- definition (which sets 'AbstractMode').
                , envRelevance              = unitRelevance
                , envQuantity               = unitQuantity
                , envHardCompileTimeMode    = False
                , envSplitOnStrict          = False
                , envDisplayFormsEnabled    = True
                , envFoldLetBindings        = True
                , envRange                  = noRange
                , envHighlightingRange      = noRange
                , envClause                 = IPNoClause
                , envCall                   = Nothing
                , envHighlightingLevel      = None
                , envHighlightingMethod     = Indirect
                , envExpandLast             = ExpandLast
                , envAppDef                 = Nothing
                , envSimplification         = NoSimplification
                , envAllowedReductions      = allReductions
                , envReduceDefs             = reduceAllDefs
                , envReconstructed          = False
                , envInjectivityDepth       = 0
                , envCompareBlocked         = False
                , envPrintDomainFreePi      = False
                , envPrintMetasBare         = False
                , envInsideDotPattern       = False
                , envUnquoteFlags           = defaultUnquoteFlags
                , envInstanceDepth          = 0
                , envIsDebugPrinting        = False
                , envPrintingPatternLambdas = []
                , envCallByNeed             = True
                , envCurrentCheckpoint      = 0
                , envCheckpoints            = Map.singleton 0 IdS
                , envGeneralizeMetas        = NoGeneralize
                , envGeneralizedVars        = Map.empty
                , envActiveBackendName      = Nothing
                , envConflComputingOverlap  = False
                , envCurrentlyElaborating   = False
                , envSyntacticEqualityFuel  = Strict.Nothing
                , envCurrentOpaqueId        = Nothing
                }

class LensTCEnv a where
  lensTCEnv :: Lens' a TCEnv

instance LensTCEnv TCEnv where
  lensTCEnv = id

data UnquoteFlags = UnquoteFlags
  { _unquoteNormalise :: Bool }
  deriving Generic

defaultUnquoteFlags :: UnquoteFlags
defaultUnquoteFlags = UnquoteFlags
  { _unquoteNormalise = False }

unquoteNormalise :: Lens' UnquoteFlags Bool
unquoteNormalise f e = f (_unquoteNormalise e) <&> \ x -> e { _unquoteNormalise = x }

eUnquoteNormalise :: Lens' TCEnv Bool
eUnquoteNormalise = eUnquoteFlags . unquoteNormalise

-- * e-prefixed lenses
------------------------------------------------------------------------

eContext :: Lens' TCEnv Context
eContext f e = f (envContext e) <&> \ x -> e { envContext = x }

eLetBindings :: Lens' TCEnv LetBindings
eLetBindings f e = f (envLetBindings e) <&> \ x -> e { envLetBindings = x }

eCurrentModule :: Lens' TCEnv ModuleName
eCurrentModule f e = f (envCurrentModule e) <&> \ x -> e { envCurrentModule = x }

eCurrentPath :: Lens' TCEnv (Maybe AbsolutePath)
eCurrentPath f e = f (envCurrentPath e) <&> \ x -> e { envCurrentPath = x }

eAnonymousModules :: Lens' TCEnv [(ModuleName, Nat)]
eAnonymousModules f e = f (envAnonymousModules e) <&> \ x -> e { envAnonymousModules = x }

eImportPath :: Lens' TCEnv [TopLevelModuleName]
eImportPath f e = f (envImportPath e) <&> \ x -> e { envImportPath = x }

eMutualBlock :: Lens' TCEnv (Maybe MutualId)
eMutualBlock f e = f (envMutualBlock e) <&> \ x -> e { envMutualBlock = x }

eTerminationCheck :: Lens' TCEnv (TerminationCheck ())
eTerminationCheck f e = f (envTerminationCheck e) <&> \ x -> e { envTerminationCheck = x }

eCoverageCheck :: Lens' TCEnv CoverageCheck
eCoverageCheck f e = f (envCoverageCheck e) <&> \ x -> e { envCoverageCheck = x }

eMakeCase :: Lens' TCEnv Bool
eMakeCase f e = f (envMakeCase e) <&> \ x -> e { envMakeCase = x }

eSolvingConstraints :: Lens' TCEnv Bool
eSolvingConstraints f e = f (envSolvingConstraints e) <&> \ x -> e { envSolvingConstraints = x }

eCheckingWhere :: Lens' TCEnv Bool
eCheckingWhere f e = f (envCheckingWhere e) <&> \ x -> e { envCheckingWhere = x }

eWorkingOnTypes :: Lens' TCEnv Bool
eWorkingOnTypes f e = f (envWorkingOnTypes e) <&> \ x -> e { envWorkingOnTypes = x }

eAssignMetas :: Lens' TCEnv Bool
eAssignMetas f e = f (envAssignMetas e) <&> \ x -> e { envAssignMetas = x }

eActiveProblems :: Lens' TCEnv (Set ProblemId)
eActiveProblems f e = f (envActiveProblems e) <&> \ x -> e { envActiveProblems = x }

eAbstractMode :: Lens' TCEnv AbstractMode
eAbstractMode f e = f (envAbstractMode e) <&> \ x -> e { envAbstractMode = x }

eRelevance :: Lens' TCEnv Relevance
eRelevance f e = f (envRelevance e) <&> \x -> e { envRelevance = x }

-- | Note that this lens does not satisfy all lens laws: If hard
-- compile-time mode is enabled, then quantities other than zero are
-- replaced by '__IMPOSSIBLE__'.

eQuantity :: Lens' TCEnv Quantity
eQuantity f e =
  if envHardCompileTimeMode e
  then f (check (envQuantity e)) <&>
       \x -> e { envQuantity = check x }
  else f (envQuantity e) <&> \x -> e { envQuantity = x }
  where
  check q
    | hasQuantity0 q = q
    | otherwise      = __IMPOSSIBLE__

eHardCompileTimeMode :: Lens' TCEnv Bool
eHardCompileTimeMode f e = f (envHardCompileTimeMode e) <&> \x -> e { envHardCompileTimeMode = x }

eSplitOnStrict :: Lens' TCEnv Bool
eSplitOnStrict f e = f (envSplitOnStrict e) <&> \ x -> e { envSplitOnStrict = x }

eDisplayFormsEnabled :: Lens' TCEnv Bool
eDisplayFormsEnabled f e = f (envDisplayFormsEnabled e) <&> \ x -> e { envDisplayFormsEnabled = x }

eFoldLetBindings :: Lens' TCEnv Bool
eFoldLetBindings f e = f (envFoldLetBindings e) <&> \ x -> e { envFoldLetBindings = x }

eRange :: Lens' TCEnv Range
eRange f e = f (envRange e) <&> \ x -> e { envRange = x }

eHighlightingRange :: Lens' TCEnv Range
eHighlightingRange f e = f (envHighlightingRange e) <&> \ x -> e { envHighlightingRange = x }

eCall :: Lens' TCEnv (Maybe (Closure Call))
eCall f e = f (envCall e) <&> \ x -> e { envCall = x }

eHighlightingLevel :: Lens' TCEnv HighlightingLevel
eHighlightingLevel f e = f (envHighlightingLevel e) <&> \ x -> e { envHighlightingLevel = x }

eHighlightingMethod :: Lens' TCEnv HighlightingMethod
eHighlightingMethod f e = f (envHighlightingMethod e) <&> \ x -> e { envHighlightingMethod = x }

eExpandLast :: Lens' TCEnv ExpandHidden
eExpandLast f e = f (envExpandLast e) <&> \ x -> e { envExpandLast = x }

eExpandLastBool :: Lens' TCEnv Bool
eExpandLastBool f e = f (isExpandLast $ envExpandLast e) <&> \ x -> e { envExpandLast = toExpandLast x }

eAppDef :: Lens' TCEnv (Maybe QName)
eAppDef f e = f (envAppDef e) <&> \ x -> e { envAppDef = x }

eSimplification :: Lens' TCEnv Simplification
eSimplification f e = f (envSimplification e) <&> \ x -> e { envSimplification = x }

eAllowedReductions :: Lens' TCEnv AllowedReductions
eAllowedReductions f e = f (envAllowedReductions e) <&> \ x -> e { envAllowedReductions = x }

eReduceDefs :: Lens' TCEnv ReduceDefs
eReduceDefs f e = f (envReduceDefs e) <&> \ x -> e { envReduceDefs = x }

eReduceDefsPair :: Lens' TCEnv (Bool, [QName])
eReduceDefsPair f e = f (fromReduceDefs $ envReduceDefs e) <&> \ x -> e { envReduceDefs = toReduceDefs x }

eReconstructed :: Lens' TCEnv Bool
eReconstructed f e = f (envReconstructed e) <&> \ x -> e { envReconstructed = x }

eInjectivityDepth :: Lens' TCEnv Int
eInjectivityDepth f e = f (envInjectivityDepth e) <&> \ x -> e { envInjectivityDepth = x }

eCompareBlocked :: Lens' TCEnv Bool
eCompareBlocked f e = f (envCompareBlocked e) <&> \ x -> e { envCompareBlocked = x }

ePrintDomainFreePi :: Lens' TCEnv Bool
ePrintDomainFreePi f e = f (envPrintDomainFreePi e) <&> \ x -> e { envPrintDomainFreePi = x }

ePrintMetasBare :: Lens' TCEnv Bool
ePrintMetasBare f e = f (envPrintMetasBare e) <&> \ x -> e { envPrintMetasBare = x }

eInsideDotPattern :: Lens' TCEnv Bool
eInsideDotPattern f e = f (envInsideDotPattern e) <&> \ x -> e { envInsideDotPattern = x }

eUnquoteFlags :: Lens' TCEnv UnquoteFlags
eUnquoteFlags f e = f (envUnquoteFlags e) <&> \ x -> e { envUnquoteFlags = x }

eInstanceDepth :: Lens' TCEnv Int
eInstanceDepth f e = f (envInstanceDepth e) <&> \ x -> e { envInstanceDepth = x }

eIsDebugPrinting :: Lens' TCEnv Bool
eIsDebugPrinting f e = f (envIsDebugPrinting e) <&> \ x -> e { envIsDebugPrinting = x }

ePrintingPatternLambdas :: Lens' TCEnv [QName]
ePrintingPatternLambdas f e = f (envPrintingPatternLambdas e) <&> \ x -> e { envPrintingPatternLambdas = x }

eCallByNeed :: Lens' TCEnv Bool
eCallByNeed f e = f (envCallByNeed e) <&> \ x -> e { envCallByNeed = x }

eCurrentCheckpoint :: Lens' TCEnv CheckpointId
eCurrentCheckpoint f e = f (envCurrentCheckpoint e) <&> \ x -> e { envCurrentCheckpoint = x }

eCheckpoints :: Lens' TCEnv (Map CheckpointId Substitution)
eCheckpoints f e = f (envCheckpoints e) <&> \ x -> e { envCheckpoints = x }

eGeneralizeMetas :: Lens' TCEnv DoGeneralize
eGeneralizeMetas f e = f (envGeneralizeMetas e) <&> \ x -> e { envGeneralizeMetas = x }

eGeneralizedVars :: Lens' TCEnv (Map QName GeneralizedValue)
eGeneralizedVars f e = f (envGeneralizedVars e) <&> \ x -> e { envGeneralizedVars = x }

eActiveBackendName :: Lens' TCEnv (Maybe BackendName)
eActiveBackendName f e = f (envActiveBackendName e) <&> \ x -> e { envActiveBackendName = x }

eConflComputingOverlap :: Lens' TCEnv Bool
eConflComputingOverlap f e = f (envConflComputingOverlap e) <&> \ x -> e { envConflComputingOverlap = x }

eCurrentlyElaborating :: Lens' TCEnv Bool
eCurrentlyElaborating f e = f (envCurrentlyElaborating e) <&> \ x -> e { envCurrentlyElaborating = x }

{-# SPECIALISE currentModality :: TCM Modality #-}
-- | The current modality.
--   Note that the returned cohesion component is always 'unitCohesion'.
currentModality :: MonadTCEnv m => m Modality
currentModality = do
  r <- viewTC eRelevance
  q <- viewTC eQuantity
  return Modality
    { modRelevance = r
    , modQuantity  = q
    , modCohesion  = unitCohesion
    }

---------------------------------------------------------------------------
-- ** Context
---------------------------------------------------------------------------

-- | The @Context@ is a stack of 'ContextEntry's.
type Context      = [ContextEntry]
type ContextEntry = Dom (Name, Type)

---------------------------------------------------------------------------
-- ** Let bindings
---------------------------------------------------------------------------

type LetBindings = Map Name (Open LetBinding)

data LetBinding = LetBinding { letOrigin :: Origin
                             , letTerm   :: Term
                             , letType   :: Dom Type
                             }
  deriving (Show, Generic)

onLetBindingType :: (Dom Type -> Dom Type) -> LetBinding -> LetBinding
onLetBindingType f b = b { letType = f $ letType b }

---------------------------------------------------------------------------
-- ** Abstract mode
---------------------------------------------------------------------------

data AbstractMode
  = AbstractMode        -- ^ Abstract things in the current module can be accessed.
  | ConcreteMode        -- ^ No abstract things can be accessed.
  | IgnoreAbstractMode  -- ^ All abstract things can be accessed.
  deriving (Show, Eq, Generic)

aDefToMode :: IsAbstract -> AbstractMode
aDefToMode AbstractDef = AbstractMode
aDefToMode ConcreteDef = ConcreteMode

aModeToDef :: AbstractMode -> Maybe IsAbstract
aModeToDef AbstractMode = Just AbstractDef
aModeToDef ConcreteMode = Just ConcreteDef
aModeToDef _ = Nothing

---------------------------------------------------------------------------
-- ** Opaque blocks
---------------------------------------------------------------------------

-- | A block of opaque definitions.
data OpaqueBlock = OpaqueBlock
  { opaqueId        :: {-# UNPACK #-} !OpaqueId
    -- ^ Unique identifier for this block.
  , opaqueUnfolding :: HashSet QName
    -- ^ Set of names we are allowed to unfold. After scope-checking,
    -- this set should be transitively closed.
  , opaqueDecls     :: HashSet QName
    -- ^ Declarations contained in this abstract block.
  , opaqueParent    :: Maybe OpaqueId
    -- ^ Pointer to an enclosing opaque block, if one exists.
  , opaqueRange     :: Range
    -- ^ Where is this opaque block?
  } deriving (Show, Generic)

instance Pretty OpaqueBlock where
  pretty (OpaqueBlock _ uf ds p _) = vcat
    $ [ "opaque (extends " <> pretty p <> ") {"
      , nest 2 "unfolds"
      ]
    ++ [ nest 4 (pretty n <> ",") | n <- List.sort $ HashSet.toList uf ]
         -- Andreas, 2023-08-10, https://github.com/agda/agda/pull/6628#discussion_r1285078454
         -- The HashSet.toList is non-deterministic, order may depend on version of @hashable@.
         -- Thus, we sort the list, so that the output isn't dependent on the specific build.
    ++ [ nest 2 "declares" ]
    ++ [ nest 4 (pretty n <+> ": _") | n <- List.sort $ HashSet.toList ds ]
    ++ [ "}" ]

instance Eq OpaqueBlock where
  xs == ys = opaqueId xs == opaqueId ys

instance Hashable OpaqueBlock where
  hashWithSalt s = hashWithSalt s . opaqueId

---------------------------------------------------------------------------
-- ** Insertion of implicit arguments
---------------------------------------------------------------------------

data ExpandHidden
  = ExpandLast      -- ^ Add implicit arguments in the end until type is no longer hidden 'Pi'.
  | DontExpandLast  -- ^ Do not append implicit arguments.
  | ReallyDontExpandLast -- ^ Makes 'doExpandLast' have no effect. Used to avoid implicit insertion of arguments to metavariables.
  deriving (Eq, Generic)

isExpandLast :: ExpandHidden -> Bool
isExpandLast ExpandLast           = True
isExpandLast DontExpandLast       = False
isExpandLast ReallyDontExpandLast = False

isDontExpandLast :: ExpandHidden -> Bool
isDontExpandLast = not . isExpandLast

toExpandLast :: Bool -> ExpandHidden
toExpandLast True  = ExpandLast
toExpandLast False = DontExpandLast

data CandidateKind
  = LocalCandidate
  | GlobalCandidate QName
  deriving (Show, Generic)

-- | A candidate solution for an instance meta is a term with its type.
--   It may be the case that the candidate is not fully applied yet or
--   of the wrong type, hence the need for the type.
data Candidate  = Candidate { candidateKind :: CandidateKind
                            , candidateTerm :: Term
                            , candidateType :: Type
                            , candidateOverlappable :: Bool
                            }
  deriving (Show, Generic)

instance Free Candidate where
  freeVars' (Candidate _ t u _) = freeVars' (t, u)


---------------------------------------------------------------------------
-- ** Checking arguments
---------------------------------------------------------------------------

data ArgsCheckState a = ACState
       { acRanges :: [Maybe Range]
         -- ^ Ranges of checked arguments, where present.
         -- e.g. inserted implicits have no correponding abstract syntax.
       , acElims  :: Elims
         -- ^ Checked and inserted arguments so far.
       , acConstraints :: [Maybe (Abs Constraint)]
         -- ^ Constraints for the head so far,
         -- i.e. before applying the correponding elim.
       , acType   :: Type
         -- ^ Type for the rest of the application.
       , acData   :: a
       }
  deriving (Show)


---------------------------------------------------------------------------
-- * Type checking warnings (aka non-fatal errors)
---------------------------------------------------------------------------

-- | A non-fatal error is an error which does not prevent us from
-- checking the document further and interacting with the user.

data Warning
  = NicifierIssue            DeclarationWarning
  | TerminationIssue         [TerminationError]
  | UnreachableClauses       QName [Range]
  -- ^ `UnreachableClauses f rs` means that the clauses in `f` whose ranges are rs
  --   are unreachable
  | CoverageIssue            QName [(Telescope, [NamedArg DeBruijnPattern])]
  -- ^ `CoverageIssue f pss` means that `pss` are not covered in `f`
  | CoverageNoExactSplit     QName [Clause]
  | InlineNoExactSplit       QName Clause
    -- ^ 'Clause' was turned into copattern matching clause(s) by an @{-# INLINE constructor #-}@
    --   and thus is not a definitional equality any more.
  | NotStrictlyPositive      QName (Seq OccursWhere)

  | UnsolvedMetaVariables    [Range]  -- ^ Do not use directly with 'warning'
  | UnsolvedInteractionMetas [Range]  -- ^ Do not use directly with 'warning'
  | UnsolvedConstraints      Constraints
    -- ^ Do not use directly with 'warning'
  | InteractionMetaBoundaries [Range]
    -- ^ Do not use directly with 'warning'

  | CantGeneralizeOverSorts [MetaId]
  | AbsurdPatternRequiresNoRHS [NamedArg DeBruijnPattern]
  | OldBuiltin               BuiltinId BuiltinId
    -- ^ In `OldBuiltin old new`, the BUILTIN old has been replaced by new
  | EmptyRewritePragma
    -- ^ If the user wrote just @{-\# REWRITE \#-}@.
  | EmptyWhere
    -- ^ An empty @where@ block is dead code.
  | IllformedAsClause String
    -- ^ If the user wrote something other than an unqualified name
    --   in the @as@ clause of an @import@ statement.
    --   The 'String' gives optionally extra explanation.
  | InvalidCharacterLiteral Char
    -- ^ A character literal Agda does not support, e.g. surrogate code points.
  | ClashesViaRenaming NameOrModule [C.Name]
    -- ^ If a `renaming' import directive introduces a name or module name clash
    --   in the exported names of a module.
    --   (See issue #4154.)
  | UselessPatternDeclarationForRecord String
    -- ^ The 'pattern' declaration is useless in the presence
    --   of either @coinductive@ or @eta-equality@.
    --   Content of 'String' is "coinductive" or "eta", resp.
  | UselessPragma Range Doc
    -- ^ Warning when pragma is useless and thus ignored.
    --   'Range' is for dead code highlighting.
  | UselessPublic
    -- ^ If the user opens a module public before the module header.
    --   (See issue #2377.)
  | UselessHiding [C.ImportedName]
    -- ^ Names in `hiding` directive that don't hide anything
    --   imported by a `using` directive.
  | UselessInline            QName
  | WrongInstanceDeclaration
  | InstanceWithExplicitArg  QName
  -- ^ An instance was declared with an implicit argument, which means it
  --   will never actually be considered by instance search.
  | InstanceNoOutputTypeName Doc
  -- ^ The type of an instance argument doesn't end in a named or
  -- variable type, so it will never be considered by instance search.
  | InstanceArgWithExplicitArg Doc
  -- ^ As InstanceWithExplicitArg, but for local bindings rather than
  --   top-level instances.
  | InversionDepthReached    QName
  -- ^ The --inversion-max-depth was reached.
  | NoGuardednessFlag        QName
  -- ^ A coinductive record was declared but neither --guardedness nor
  --   --sized-types is enabled.

  -- Generic warnings for one-off things
  | GenericWarning           Doc
    -- ^ Harmless generic warning (not an error)

  -- Safe flag errors
  | SafeFlagPostulate C.Name
  | SafeFlagPragma [String]                -- ^ Unsafe OPTIONS.
  | SafeFlagWithoutKFlagPrimEraseEquality
  | WithoutKFlagPrimEraseEquality
  | OptionWarning            OptionWarning
  | ParseWarning             ParseWarning
  | LibraryWarning           LibWarning
  | DeprecationWarning String String String
    -- ^ `DeprecationWarning old new version`:
    --   `old` is deprecated, use `new` instead. This will be an error in Agda `version`.
  | UserWarning Text
    -- ^ User-defined warning (e.g. to mention that a name is deprecated)
  | DuplicateUsing (List1 C.ImportedName)
    -- ^ Duplicate mentions of the same name in @using@ directive(s).
  | FixityInRenamingModule (List1 Range)
    -- ^ Fixity of modules cannot be changed via renaming (since modules have no fixity).
  | ModuleDoesntExport C.QName [C.Name] [C.Name] [C.ImportedName]
    -- ^ Some imported names are not actually exported by the source module.
    --   The second argument is the names that could be exported.
    --   The third  argument is the module names that could be exported.
  | InfectiveImport Doc
    -- ^ Importing a file using an infective option into one which doesn't
  | CoInfectiveImport Doc
    -- ^ Importing a file not using a coinfective option from one which does
  | RewriteNonConfluent Term Term Term Doc
    -- ^ Confluence checker found critical pair and equality checking
    --   resulted in a type error
  | RewriteMaybeNonConfluent Term Term [Doc]
    -- ^ Confluence checker got stuck on computing overlap between two
    --   rewrite rules
  | RewriteAmbiguousRules Term Term Term
    -- ^ The global confluence checker found a term @u@ that reduces
    --   to both @v1@ and @v2@ and there is no rule to resolve the
    --   ambiguity.
  | RewriteMissingRule Term Term Term
    -- ^ The global confluence checker found a term @u@ that reduces
    --   to @v@, but @v@ does not reduce to @rho(u)@.
  | PragmaCompileErased BackendName QName
    -- ^ COMPILE directive for an erased symbol
  | NotInScopeW [C.QName]
    -- ^ Out of scope error we can recover from
  | UnsupportedIndexedMatch Doc
    -- ^ Was not able to compute a full equivalence when splitting.
  | AsPatternShadowsConstructorOrPatternSynonym Bool
    -- ^ The as-name in an as-pattern may not shadow a constructor (@False@)
    --   or pattern synonym name (@True@),
    --   because this can be confusing to read.
  | PatternShadowsConstructor C.Name A.QName
    -- ^ A pattern variable has the name of a constructor
    --   (data constructor or matchable record constructor).
  | PlentyInHardCompileTimeMode QωOrigin
    -- ^ Explicit use of @@ω@ or @@plenty@ in hard compile-time mode.
  | RecordFieldWarning RecordFieldWarning
  | NotAffectedByOpaque
  | UnfoldTransparentName QName
  | UselessOpaque

  -- Cubical
  | FaceConstraintCannotBeHidden ArgInfo
    -- ^ Face constraint patterns @(i = 0)@ must be visible arguments.
  | FaceConstraintCannotBeNamed NamedName
    -- ^ Face constraint patterns @(i = 0)@ must be unnamed arguments.
  deriving (Show, Generic)

recordFieldWarningToError :: RecordFieldWarning -> TypeError
recordFieldWarningToError = \case
  W.DuplicateFields    xrs -> DuplicateFields    $ map fst xrs
  W.TooManyFields q ys xrs -> TooManyFields q ys $ map fst xrs

warningName :: Warning -> WarningName
warningName = \case
  -- special cases
  NicifierIssue dw             -> declarationWarningName dw
  OptionWarning ow             -> optionWarningName ow
  ParseWarning pw              -> parseWarningName pw
  LibraryWarning lw            -> libraryWarningName lw
  -- scope- and type-checking errors
  AsPatternShadowsConstructorOrPatternSynonym{} -> AsPatternShadowsConstructorOrPatternSynonym_
  PatternShadowsConstructor{}  -> PatternShadowsConstructor_
  AbsurdPatternRequiresNoRHS{} -> AbsurdPatternRequiresNoRHS_
  CantGeneralizeOverSorts{}    -> CantGeneralizeOverSorts_
  CoverageIssue{}              -> CoverageIssue_
  CoverageNoExactSplit{}       -> CoverageNoExactSplit_
  InlineNoExactSplit{}         -> InlineNoExactSplit_
  DeprecationWarning{}         -> DeprecationWarning_
  EmptyRewritePragma           -> EmptyRewritePragma_
  EmptyWhere                   -> EmptyWhere_
  IllformedAsClause{}          -> IllformedAsClause_
  WrongInstanceDeclaration{}   -> WrongInstanceDeclaration_
  InstanceWithExplicitArg{}    -> InstanceWithExplicitArg_
  InstanceNoOutputTypeName{}   -> InstanceNoOutputTypeName_
  InstanceArgWithExplicitArg{} -> InstanceArgWithExplicitArg_
  DuplicateUsing{}             -> DuplicateUsing_
  FixityInRenamingModule{}     -> FixityInRenamingModule_
  InvalidCharacterLiteral{}    -> InvalidCharacterLiteral_
  UselessPragma{}              -> UselessPragma_
  GenericWarning{}             -> GenericWarning_
  InversionDepthReached{}      -> InversionDepthReached_
  InteractionMetaBoundaries{}  -> InteractionMetaBoundaries_{}
  ModuleDoesntExport{}         -> ModuleDoesntExport_
  NoGuardednessFlag{}          -> NoGuardednessFlag_
  NotInScopeW{}                -> NotInScope_
  NotStrictlyPositive{}        -> NotStrictlyPositive_
  UnsupportedIndexedMatch{}    -> UnsupportedIndexedMatch_
  OldBuiltin{}                 -> OldBuiltin_
  SafeFlagPostulate{}          -> SafeFlagPostulate_
  SafeFlagPragma{}             -> SafeFlagPragma_
  SafeFlagWithoutKFlagPrimEraseEquality -> SafeFlagWithoutKFlagPrimEraseEquality_
  WithoutKFlagPrimEraseEquality -> WithoutKFlagPrimEraseEquality_
  TerminationIssue{}           -> TerminationIssue_
  UnreachableClauses{}         -> UnreachableClauses_
  UnsolvedInteractionMetas{}   -> UnsolvedInteractionMetas_
  UnsolvedConstraints{}        -> UnsolvedConstraints_
  UnsolvedMetaVariables{}      -> UnsolvedMetaVariables_
  UselessHiding{}              -> UselessHiding_
  UselessInline{}              -> UselessInline_
  UselessPublic{}              -> UselessPublic_
  UselessPatternDeclarationForRecord{} -> UselessPatternDeclarationForRecord_
  ClashesViaRenaming{}         -> ClashesViaRenaming_
  UserWarning{}                -> UserWarning_
  InfectiveImport{}            -> InfectiveImport_
  CoInfectiveImport{}          -> CoInfectiveImport_
  RewriteNonConfluent{}        -> RewriteNonConfluent_
  RewriteMaybeNonConfluent{}   -> RewriteMaybeNonConfluent_
  RewriteAmbiguousRules{}      -> RewriteAmbiguousRules_
  RewriteMissingRule{}         -> RewriteMissingRule_
  PragmaCompileErased{}        -> PragmaCompileErased_
  PlentyInHardCompileTimeMode{}
                               -> PlentyInHardCompileTimeMode_
  -- record field warnings
  RecordFieldWarning w -> case w of
    W.DuplicateFields{}   -> DuplicateFields_
    W.TooManyFields{}     -> TooManyFields_

  NotAffectedByOpaque{}   -> NotAffectedByOpaque_
  UselessOpaque{}         -> UselessOpaque_
  UnfoldTransparentName{} -> UnfoldTransparentName_

  -- Cubical
  FaceConstraintCannotBeHidden{} -> FaceConstraintCannotBeHidden_
  FaceConstraintCannotBeNamed{}  -> FaceConstraintCannotBeNamed_

data TCWarning
  = TCWarning
    { tcWarningLocation :: CallStack
        -- ^ Location in the internal Agda source code location where the error raised
    , tcWarningRange    :: Range
        -- ^ Range where the warning was raised
    , tcWarning         :: Warning
        -- ^ The warning itself
    , tcWarningPrintedWarning :: Doc
        -- ^ The warning printed in the state and environment where it was raised
    , tcWarningCached :: Bool
        -- ^ Should the warning be affected by caching.
    }
  deriving (Show, Generic)

tcWarningOrigin :: TCWarning -> SrcFile
tcWarningOrigin = rangeFile . tcWarningRange

instance HasRange TCWarning where
  getRange = tcWarningRange

-- used for merging lists of warnings
instance Eq TCWarning where
  (==) = (==) `on` tcWarningPrintedWarning

---------------------------------------------------------------------------
-- * Type checking errors
---------------------------------------------------------------------------

-- | Information about a call.

data CallInfo = CallInfo
  { callInfoTarget :: QName
    -- ^ Target function name.  (Contains its range.)
  , callInfoCall :: Closure Term
    -- ^ To be formatted representation of the call.
  } deriving (Show, Generic)
    -- no Eq, Ord instances: too expensive! (see issues 851, 852)

instance HasRange CallInfo where
  getRange = getRange . callInfoTarget

-- | We only 'show' the name of the callee.
instance Pretty CallInfo where pretty = pretty . callInfoTarget

-- | Information about a mutual block which did not pass the
-- termination checker.

data TerminationError = TerminationError
  { termErrFunctions :: [QName]
    -- ^ The functions which failed to check. (May not include
    -- automatically generated functions.)
  , termErrCalls :: [CallInfo]
    -- ^ The problematic call sites.
  } deriving (Show, Generic)

-- | The reason for an 'ErasedDatatype' error.

data ErasedDatatypeReason
  = SeveralConstructors
    -- ^ There are several constructors.
  | NoErasedMatches
    -- ^ The flag @--erased-matches@ is not used.
  | NoK
    -- ^ The K rule is not activated.
  deriving (Show, Generic)

-- | Error when splitting a pattern variable into possible constructor patterns.
data SplitError
  = NotADatatype        (Closure Type)  -- ^ Neither data type nor record.
  | BlockedType Blocker (Closure Type)  -- ^ Type could not be sufficiently reduced.
  | ErasedDatatype ErasedDatatypeReason (Closure Type)
                                        -- ^ Data type, but in erased position.
  | CoinductiveDatatype (Closure Type)  -- ^ Split on codata not allowed.
  -- UNUSED, but keep!
  -- -- | NoRecordConstructor Type  -- ^ record type, but no constructor
  | UnificationStuck
    { cantSplitBlocker  :: Maybe Blocker -- ^ Blocking metavariable (if any)
    , cantSplitConName  :: QName        -- ^ Constructor.
    , cantSplitTel      :: Telescope    -- ^ Context for indices.
    , cantSplitConIdx   :: Args         -- ^ Inferred indices (from type of constructor).
    , cantSplitGivenIdx :: Args         -- ^ Expected indices (from checking pattern).
    , cantSplitFailures :: [UnificationFailure] -- ^ Reason(s) why unification got stuck.
    }
  | CosplitCatchall
      -- ^ Copattern split with a catchall
  | CosplitNoTarget
      -- ^ We do not know the target type of the clause.
  | CosplitNoRecordType (Closure Type)
      -- ^ Target type is not a record type.
  | CannotCreateMissingClause QName (Telescope,[NamedArg DeBruijnPattern]) Doc (Closure (Abs Type))

  | GenericSplitError String
  deriving (Show, Generic)

data NegativeUnification
  = UnifyConflict Telescope Term Term
  | UnifyCycle Telescope Int Term
  deriving (Show, Generic)

data UnificationFailure
  = UnifyIndicesNotVars Telescope Type Term Term Args -- ^ Failed to apply injectivity to constructor of indexed datatype
  | UnifyRecursiveEq Telescope Type Int Term          -- ^ Can't solve equation because variable occurs in (type of) lhs
  | UnifyReflexiveEq Telescope Type Term              -- ^ Can't solve reflexive equation because --without-K is enabled
  | UnifyUnusableModality Telescope Type Int Term Modality  -- ^ Can't solve equation because solution modality is less "usable"
  deriving (Show, Generic)

data UnquoteError
  = BadVisibility String (Arg I.Term)
  | ConInsteadOfDef QName String String
  | DefInsteadOfCon QName String String
  | NonCanonical String I.Term
  | BlockedOnMeta TCState Blocker
  | UnquotePanic String
  deriving (Show, Generic)

data TypeError
        = InternalError String
        | NotImplemented String
        | NotSupported String
        | CompilationError String
        | PropMustBeSingleton
        | DataMustEndInSort Term
{- UNUSED
        | DataTooManyParameters
            -- ^ In @data D xs where@ the number of parameters @xs@ does not fit the
            --   the parameters given in the forward declaraion @data D Gamma : T@.
-}
        | ShouldEndInApplicationOfTheDatatype Type
            -- ^ The target of a constructor isn't an application of its
            -- datatype. The 'Type' records what it does target.
        | ShouldBeAppliedToTheDatatypeParameters Term Term
            -- ^ The target of a constructor isn't its datatype applied to
            --   something that isn't the parameters. First term is the correct
            --   target and the second term is the actual target.
        | ShouldBeApplicationOf Type QName
            -- ^ Expected a type to be an application of a particular datatype.
        | ConstructorPatternInWrongDatatype QName QName -- ^ constructor, datatype
        | CantResolveOverloadedConstructorsTargetingSameDatatype QName (List1 QName)
          -- ^ Datatype, constructors.
        | DoesNotConstructAnElementOf QName Type -- ^ constructor, type
        | WrongHidingInLHS
            -- ^ The left hand side of a function definition has a hidden argument
            --   where a non-hidden was expected.
        | WrongHidingInLambda Type
            -- ^ Expected a non-hidden function and found a hidden lambda.
        | WrongHidingInApplication Type
            -- ^ A function is applied to a hidden argument where a non-hidden was expected.
        | WrongHidingInProjection QName
        | IllegalHidingInPostfixProjection (NamedArg C.Expr)
        | WrongNamedArgument (NamedArg A.Expr) [NamedName]
            -- ^ A function is applied to a hidden named argument it does not have.
            -- The list contains names of possible hidden arguments at this point.
        | WrongIrrelevanceInLambda
            -- ^ Wrong user-given relevance annotation in lambda.
        | WrongQuantityInLambda
            -- ^ Wrong user-given quantity annotation in lambda.
        | WrongCohesionInLambda
            -- ^ Wrong user-given cohesion annotation in lambda.
        | QuantityMismatch Quantity Quantity
            -- ^ The given quantity does not correspond to the expected quantity.
        | HidingMismatch Hiding Hiding
            -- ^ The given hiding does not correspond to the expected hiding.
        | RelevanceMismatch Relevance Relevance
            -- ^ The given relevance does not correspond to the expected relevane.
        | UninstantiatedDotPattern A.Expr
        | ForcedConstructorNotInstantiated A.Pattern
        | IllformedProjectionPatternAbstract A.Pattern
        | IllformedProjectionPatternConcrete C.Pattern
        | CannotEliminateWithPattern (Maybe Blocker) (NamedArg A.Pattern) Type
        | CannotEliminateWithProjection (Arg Type) Bool QName
        | WrongNumberOfConstructorArguments QName Nat Nat
        | ShouldBeEmpty Type [DeBruijnPattern]
        | ShouldBeASort Type
            -- ^ The given type should have been a sort.
        | ShouldBePi Type
            -- ^ The given type should have been a pi.
        | ShouldBePath Type
        | ShouldBeRecordType Type
        | ShouldBeRecordPattern DeBruijnPattern
        | NotAProjectionPattern (NamedArg A.Pattern)
        | NotAProperTerm
        | InvalidTypeSort Sort
            -- ^ This sort is not a type expression.
        | InvalidType Term
            -- ^ This term is not a type expression.
        | FunctionTypeInSizeUniv Term
            -- ^ This term, a function type constructor, lives in
            --   @SizeUniv@, which is not allowed.
        | SplitOnIrrelevant (Dom Type)
        | SplitOnUnusableCohesion (Dom Type)
        -- UNUSED: -- | SplitOnErased (Dom Type)
        | SplitOnNonVariable Term Type
        | SplitOnNonEtaRecord QName
        | SplitOnAbstract QName
        | SplitOnUnchecked QName
        | SplitOnPartial (Dom Type)
        | SplitInProp DataOrRecordE
        | DefinitionIsIrrelevant QName
        | DefinitionIsErased QName
        | VariableIsIrrelevant Name
        | VariableIsErased Name
        | VariableIsOfUnusableCohesion Name Cohesion
        | UnequalLevel Comparison Level Level
        | UnequalTerms Comparison Term Term CompareAs
        | UnequalTypes Comparison Type Type
--      | UnequalTelescopes Comparison Telescope Telescope -- UNUSED
        | UnequalRelevance Comparison Term Term
            -- ^ The two function types have different relevance.
        | UnequalQuantity Comparison Term Term
            -- ^ The two function types have different relevance.
        | UnequalCohesion Comparison Term Term
            -- ^ The two function types have different cohesion.
        | UnequalFiniteness Comparison Term Term
            -- ^ One of the function types has a finite domain (i.e. is a @Partia@l@) and the other isonot.
        | UnequalHiding Term Term
            -- ^ The two function types have different hiding.
        | UnequalSorts Sort Sort
        | UnequalBecauseOfUniverseConflict Comparison Term Term
        | NotLeqSort Sort Sort
        | MetaCannotDependOn MetaId Nat
            -- ^ The arguments are the meta variable and the parameter that it wants to depend on.
        | MetaOccursInItself MetaId
        | MetaIrrelevantSolution MetaId Term
        | MetaErasedSolution MetaId Term
        | GenericError String
        | GenericDocError Doc
        | SortOfSplitVarError (Maybe Blocker) Doc
          -- ^ the meta is what we might be blocked on.
        | BuiltinMustBeConstructor BuiltinId A.Expr
        | NoSuchBuiltinName String
        | DuplicateBuiltinBinding BuiltinId Term Term
        | NoBindingForBuiltin BuiltinId
        | NoBindingForPrimitive PrimitiveId
        | NoSuchPrimitiveFunction String
        | DuplicatePrimitiveBinding PrimitiveId QName QName
        | WrongArgInfoForPrimitive PrimitiveId ArgInfo ArgInfo
        | ShadowedModule C.Name [A.ModuleName]
        | BuiltinInParameterisedModule BuiltinId
        | IllegalDeclarationInDataDefinition [C.Declaration]
            -- ^ The declaration list comes from a single 'C.NiceDeclaration'.
        | IllegalLetInTelescope C.TypedBinding
        | IllegalPatternInTelescope C.Binder
        | NoRHSRequiresAbsurdPattern [NamedArg A.Pattern]
        | TooManyFields QName [C.Name] [C.Name]
          -- ^ Record type, fields not supplied by user, non-fields but supplied.
        | DuplicateFields [C.Name]
        | DuplicateConstructors [C.Name]
        | WithOnFreeVariable A.Expr Term
        | UnexpectedWithPatterns [A.Pattern]
        | WithClausePatternMismatch A.Pattern (NamedArg DeBruijnPattern)
        | IllTypedPatternAfterWithAbstraction A.Pattern
        | FieldOutsideRecord
        | ModuleArityMismatch A.ModuleName Telescope [NamedArg A.Expr]
        | GeneralizeCyclicDependency
        | GeneralizeUnsolvedMeta
        | ReferencesFutureVariables Term (List1.NonEmpty Int) (Arg Term) Int
          -- ^ The first term references the given list of variables,
          -- which are in "the future" with respect to the given lock
          -- (and its leftmost variable)
        | DoesNotMentionTicks Term Type (Arg Term)
          -- ^ Arguments: later term, its type, lock term. The lock term
          -- does not mention any @lock variables.
        | MismatchedProjectionsError QName QName
        | AttributeKindNotEnabled String String String
        | InvalidProjectionParameter (NamedArg A.Expr)
        | TacticAttributeNotAllowed
        | CannotRewriteByNonEquation Type
        | MacroResultTypeMismatch Type
        | NamedWhereModuleInRefinedContext [Term] [String]
        | CubicalPrimitiveNotFullyApplied QName
        | TooManyArgumentsToLeveledSort QName
        | TooManyArgumentsToUnivOmega QName
        | ComatchingDisabledForRecord QName
        | BuiltinMustBeIsOne Term
        | IllegalRewriteRule QName IllegalRewriteRuleReason
        | IncorrectTypeForRewriteRelation Term IncorrectTypeForRewriteRelationReason
    -- Data errors
        | UnexpectedParameter A.LamBinding
        | NoParameterOfName ArgName
        | UnexpectedModalityAnnotationInParameter A.LamBinding
        | ExpectedBindingForParameter (Dom Type) (Abs Type)
        | UnexpectedTypeSignatureForParameter (List1 (NamedArg A.Binder))
        | SortDoesNotAdmitDataDefinitions QName Sort
        | SortCannotDependOnItsIndex QName Type
    -- Coverage errors
-- UNUSED:        | IncompletePatternMatching Term [Elim] -- can only happen if coverage checking is switched off
        | SplitError SplitError
        | ImpossibleConstructor QName NegativeUnification
    -- Positivity errors
        | TooManyPolarities QName Int
    -- Import errors
        | LocalVsImportedModuleClash ModuleName
        | SolvedButOpenHoles
          -- ^ Some interaction points (holes) have not been filled by user.
          --   There are not 'UnsolvedMetas' since unification solved them.
          --   This is an error, since interaction points are never filled
          --   without user interaction.
        | CyclicModuleDependency [TopLevelModuleName]
        | FileNotFound TopLevelModuleName [AbsolutePath]
        | OverlappingProjects AbsolutePath TopLevelModuleName TopLevelModuleName
        | AmbiguousTopLevelModuleName TopLevelModuleName [AbsolutePath]
        | ModuleNameUnexpected TopLevelModuleName TopLevelModuleName
          -- ^ Found module name, expected module name.
        | ModuleNameDoesntMatchFileName TopLevelModuleName [AbsolutePath]
        | ClashingFileNamesFor ModuleName [AbsolutePath]
        | ModuleDefinedInOtherFile TopLevelModuleName AbsolutePath AbsolutePath
          -- ^ Module name, file from which it was loaded, file which
          -- the include path says contains the module.
    -- Scope errors
        | BothWithAndRHS
        | AbstractConstructorNotInScope A.QName
        | NotInScope [C.QName]
        | NoSuchModule C.QName
        | AmbiguousName C.QName AmbiguousNameReason
        | AmbiguousModule C.QName (List1 A.ModuleName)
        | AmbiguousField C.Name [A.ModuleName]
        | AmbiguousConstructor QName [QName]
        | ClashingDefinition C.QName A.QName (Maybe NiceDeclaration)
        | ClashingModule A.ModuleName A.ModuleName
        | ClashingImport C.Name A.QName
        | ClashingModuleImport C.Name A.ModuleName
        | DuplicateImports C.QName [C.ImportedName]
        | InvalidPattern C.Pattern
        | RepeatedVariablesInPattern [C.Name]
        | GeneralizeNotSupportedHere A.QName
        | GeneralizedVarInLetOpenedModule A.QName
        | MultipleFixityDecls [(C.Name, [Fixity'])]
        | MultiplePolarityPragmas [C.Name]
    -- Concrete to Abstract errors
        | NotAModuleExpr C.Expr
            -- ^ The expr was used in the right hand side of an implicit module
            --   definition, but it wasn't of the form @m Delta@.
        | NotAnExpression C.Expr
        | NotAValidLetBinding NiceDeclaration
        | NotValidBeforeField NiceDeclaration
        | NothingAppliedToHiddenArg C.Expr
        | NothingAppliedToInstanceArg C.Expr
    -- Pattern synonym errors
        | BadArgumentsToPatternSynonym A.AmbiguousQName
        | TooFewArgumentsToPatternSynonym A.AmbiguousQName
        | CannotResolveAmbiguousPatternSynonym (List1 (A.QName, A.PatternSynDefn))
        | UnusedVariableInPatternSynonym
        | UnboundVariablesInPatternSynonym [A.Name]
    -- Operator errors
        | NoParseForApplication (List2 C.Expr)
        | AmbiguousParseForApplication (List2 C.Expr) (List1 C.Expr)
        | NoParseForLHS LHSOrPatSyn [C.Pattern] C.Pattern
            -- ^ The list contains patterns that failed to be interpreted.
            --   If it is non-empty, the first entry could be printed as error hint.
        | AmbiguousParseForLHS LHSOrPatSyn C.Pattern [C.Pattern]
            -- ^ Pattern and its possible interpretations.
        | AmbiguousProjection QName [QName]
        | AmbiguousOverloadedProjection (List1 QName) Doc
        | OperatorInformation [NotationSection] TypeError
{- UNUSED
        | NoParseForPatternSynonym C.Pattern
        | AmbiguousParseForPatternSynonym C.Pattern [C.Pattern]
-}
    -- Usage errors
    -- Instance search errors
        | InstanceNoCandidate Type [(Term, TCErr)]
    -- Reflection errors
        | UnquoteFailed UnquoteError
        | DeBruijnIndexOutOfScope Nat Telescope [Name]
    -- Language option errors
        | NeedOptionCopatterns
        | NeedOptionRewriting
        | NeedOptionProp
        | NeedOptionTwoLevel
    -- Failure associated to warnings
        | NonFatalErrors [TCWarning]
    -- Instance search errors
        | InstanceSearchDepthExhausted Term Type Int
        | TriedToCopyConstrainedPrim QName
          deriving (Show, Generic)

type DataOrRecordE = DataOrRecord' InductionAndEta

data InductionAndEta = InductionAndEta
  { recordInduction   :: Maybe Induction
  , recordEtaEquality :: EtaEquality
  } deriving (Show, Generic)

-- Reason, why rewrite rule is invalid
data IllegalRewriteRuleReason
  = LHSNotDefOrConstr
  | VariablesNotBoundByLHS IntSet
  | VariablesBoundMoreThanOnce IntSet
  | LHSReducesTo Term Term
  | HeadSymbolIsProjection QName
  | HeadSymbolIsProjectionLikeFunction QName
  | HeadSymbolNotPostulateFunctionConstructor QName
  | HeadSymbolDefContainsMetas QName
  | ConstructorParamsNotGeneral ConHead Args
  | ContainsUnsolvedMetaVariables (Set MetaId)
  | BlockedOnProblems (Set ProblemId)
  | RequiresDefinitions (Set QName)
  | DoesNotTargetRewriteRelation
  | BeforeFunctionDefinition
  | EmptyReason
    deriving (Show, Generic)

-- Reason, why type for rewrite rule is incorrect
data IncorrectTypeForRewriteRelationReason
  = ShouldAcceptAtLeastTwoArguments
  | FinalTwoArgumentsNotVisible
  | TypeDoesNotEndInSort Type Telescope
    deriving (Show, Generic)

-- | Distinguish error message when parsing lhs or pattern synonym, resp.
data LHSOrPatSyn = IsLHS | IsPatSyn
  deriving (Eq, Show, Generic)

-- | Type-checking errors.

data TCErr
  = TypeError
    { tcErrLocation :: CallStack
       -- ^ Location in the internal Agda source code where the error was raised
    , tcErrState    :: TCState
        -- ^ The state in which the error was raised.
    , tcErrClosErr  :: Closure TypeError
        -- ^ The environment in which the error as raised plus the error.
    }
  | Exception Range Doc
  | IOException TCState Range E.IOException
    -- ^ The first argument is the state in which the error was
    -- raised.
  | PatternErr Blocker
      -- ^ The exception which is usually caught.
      --   Raised for pattern violations during unification ('assignV')
      --   but also in other situations where we want to backtrack.
      --   Contains an unblocker to control when the computation should
      --   be retried.

instance Show TCErr where
  show (TypeError _ _ e)   = prettyShow (envRange $ clEnv e) ++ ": " ++ show (clValue e)
  show (Exception r d)     = prettyShow r ++ ": " ++ render d
  show (IOException _ r e) = prettyShow r ++ ": " ++
                             E.displayException e
  show PatternErr{}        = "Pattern violation (you shouldn't see this)"

instance HasRange TCErr where
  getRange (TypeError _ _ cl)  = envRange $ clEnv cl
  getRange (Exception r _)     = r
  getRange (IOException s r _) = r
  getRange PatternErr{}        = noRange

instance E.Exception TCErr

-- | Assorted warnings and errors to be displayed to the user
data WarningsAndNonFatalErrors = WarningsAndNonFatalErrors
  { tcWarnings     :: [TCWarning]
  , nonFatalErrors :: [TCWarning]
  }

-----------------------------------------------------------------------------
-- * Accessing options
-----------------------------------------------------------------------------

instance MonadIO m => HasOptions (TCMT m) where
  pragmaOptions = useTC stPragmaOptions
  {-# INLINE pragmaOptions #-}

  commandLineOptions = do
    p  <- useTC stPragmaOptions
    cl <- stPersistentOptions . stPersistentState <$> getTC
    return $ cl { optPragmaOptions = p }
  {-# SPECIALIZE commandLineOptions :: TCM CommandLineOptions #-}

-- HasOptions lifts through monad transformers
-- (see default signatures in the HasOptions class).

sizedTypesOption :: HasOptions m => m Bool
sizedTypesOption = optSizedTypes <$> pragmaOptions
{-# INLINE sizedTypesOption #-}

typeBasedTerminationOption :: HasOptions m => m Bool
typeBasedTerminationOption = optTypeBasedTermination <$> pragmaOptions
{-# INLINE typeBasedTerminationOption #-}

syntaxBasedTerminationOption :: HasOptions m => m Bool
syntaxBasedTerminationOption = optSyntaxBasedTermination <$> pragmaOptions
{-# INLINE syntaxBasedTerminationOption #-}

guardednessOption :: HasOptions m => m Bool
guardednessOption = optGuardedness <$> pragmaOptions
{-# INLINE guardednessOption #-}

withoutKOption :: HasOptions m => m Bool
withoutKOption = optWithoutK <$> pragmaOptions
{-# INLINE withoutKOption #-}

cubicalCompatibleOption :: HasOptions m => m Bool
cubicalCompatibleOption = optCubicalCompatible <$> pragmaOptions
{-# INLINE cubicalCompatibleOption #-}

enableCaching :: HasOptions m => m Bool
enableCaching = optCaching <$> pragmaOptions
{-# INLINE enableCaching #-}

-----------------------------------------------------------------------------
-- * The reduce monad
-----------------------------------------------------------------------------

-- | Environment of the reduce monad.
data ReduceEnv = ReduceEnv
  { redEnv  :: TCEnv    -- ^ Read only access to environment.
  , redSt   :: TCState  -- ^ Read only access to state (signature, metas...).
  , redPred :: Maybe (MetaId -> ReduceM Bool)
    -- ^ An optional predicate that is used by 'instantiate'' and
    -- 'instantiateFull'': meta-variables are only instantiated if
    -- they satisfy this predicate.
  }

mapRedEnv :: (TCEnv -> TCEnv) -> ReduceEnv -> ReduceEnv
mapRedEnv f s = s { redEnv = f (redEnv s) }
{-# INLINE mapRedEnv #-}

mapRedSt :: (TCState -> TCState) -> ReduceEnv -> ReduceEnv
mapRedSt f s = s { redSt = f (redSt s) }
{-# INLINE mapRedSt #-}

mapRedEnvSt :: (TCEnv -> TCEnv) -> (TCState -> TCState) -> ReduceEnv
            -> ReduceEnv
mapRedEnvSt f g (ReduceEnv e s p) = ReduceEnv (f e) (g s) p
{-# INLINE mapRedEnvSt #-}

-- Lenses
reduceEnv :: Lens' ReduceEnv TCEnv
reduceEnv f s = f (redEnv s) <&> \ e -> s { redEnv = e }
{-# INLINE reduceEnv #-}

reduceSt :: Lens' ReduceEnv TCState
reduceSt f s = f (redSt s) <&> \ e -> s { redSt = e }
{-# INLINE reduceSt #-}

newtype ReduceM a = ReduceM { unReduceM :: ReduceEnv -> a }
--  deriving (Functor, Applicative, Monad)

unKleisli :: (a -> ReduceM b) -> ReduceM (a -> b)
unKleisli f = ReduceM $ \ env x -> unReduceM (f x) env

onReduceEnv :: (ReduceEnv -> ReduceEnv) -> ReduceM a -> ReduceM a
onReduceEnv f (ReduceM m) = ReduceM (m . f)
{-# INLINE onReduceEnv #-}

fmapReduce :: (a -> b) -> ReduceM a -> ReduceM b
fmapReduce f (ReduceM m) = ReduceM $ \ e -> f $! m e
{-# INLINE fmapReduce #-}

-- Andreas, 2021-05-12, issue #5379:
-- It seems more stable to force to evaluate @mf <*> ma@
-- from left to right, for the sake of printing
-- debug messages in order.
apReduce :: ReduceM (a -> b) -> ReduceM a -> ReduceM b
apReduce (ReduceM f) (ReduceM x) = ReduceM $ \ e ->
  let g = f e
      a = x e
  in  g `pseq` a `pseq` g a
{-# INLINE apReduce #-}


-- Andreas, 2021-05-12, issue #5379
-- Since the MonadDebug instance of ReduceM is implemented via
-- unsafePerformIO, we need to force results that later
-- computations do not depend on, otherwise we lose debug messages.
thenReduce :: ReduceM a -> ReduceM b -> ReduceM b
thenReduce (ReduceM x) (ReduceM y) = ReduceM $ \ e -> x e `pseq` y e
{-# INLINE thenReduce #-}


-- Andreas, 2021-05-14:
-- `seq` does not force evaluation order, the optimizier is allowed to replace
-- @
--    a `seq` b`
-- @
-- by:
-- @
--    b `seq` a `seq` b
-- @
-- see https://hackage.haskell.org/package/parallel/docs/Control-Parallel.html
--
-- In contrast, `pseq` is only strict in its first argument, so such a permutation
-- is forbidden.
-- If we want to ensure that debug messages are printed before exceptions are
-- propagated, we need to use `pseq`, as in:
-- @
--    unsafePerformIO (putStrLn "Black hawk is going down...") `pseq` throw HitByRPG
-- @
beforeReduce :: ReduceM a -> ReduceM b -> ReduceM a
beforeReduce (ReduceM x) (ReduceM y) = ReduceM $ \ e ->
  let a = x e
  in  a `pseq` y e `pseq` a
{-# INLINE beforeReduce #-}

bindReduce :: ReduceM a -> (a -> ReduceM b) -> ReduceM b
bindReduce (ReduceM m) f = ReduceM $ \ e -> unReduceM (f $! m e) e
{-# INLINE bindReduce #-}

instance Functor ReduceM where
  fmap = fmapReduce

instance Applicative ReduceM where
  pure x = ReduceM (const x)
  (<*>) = apReduce
  (*>)  = thenReduce
  (<*)  = beforeReduce

instance Monad ReduceM where
  return = pure
  (>>=) = bindReduce
  (>>) = (*>)

instance Fail.MonadFail ReduceM where
  fail = error

instance ReadTCState ReduceM where
  getTCState = ReduceM redSt
  locallyTCState l f = onReduceEnv $ mapRedSt $ over l f

runReduceM :: ReduceM a -> TCM a
runReduceM m = TCM $ \ r e -> do
  s <- readIORef r
  E.evaluate $ unReduceM m $ ReduceEnv e s Nothing
  -- Andreas, 2021-05-13, issue #5379
  -- This was the following, which is apparently not strict enough
  -- to force all unsafePerformIOs...
  -- runReduceM m = do
  --   e <- askTC
  --   s <- getTC
  --   return $! unReduceM m (ReduceEnv e s)

runReduceF :: (a -> ReduceM b) -> TCM (a -> b)
runReduceF f = do
  e <- askTC
  s <- getTC
  return $ \x -> unReduceM (f x) (ReduceEnv e s Nothing)

instance MonadTCEnv ReduceM where
  askTC   = ReduceM redEnv
  localTC = onReduceEnv . mapRedEnv

-- Andrea comments (https://github.com/agda/agda/issues/1829#issuecomment-522312084):
--
--   useR forces the result of projecting the lens,
--   this usually prevents retaining the whole structure when we only need a field.
--
-- This fixes (or contributes to the fix of) the space leak issue #1829 (caching).
useR :: (ReadTCState m) => Lens' TCState a -> m a
useR l = do
  !x <- getTCState <&> (^. l)
  return x
{-# INLINE useR #-}

askR :: ReduceM ReduceEnv
askR = ReduceM ask
{-# INLINE askR #-}

localR :: (ReduceEnv -> ReduceEnv) -> ReduceM a -> ReduceM a
localR f = ReduceM . local f . unReduceM
{-# INLINE localR #-}

instance HasOptions ReduceM where
  pragmaOptions      = useR stPragmaOptions
  commandLineOptions = do
    p  <- useR stPragmaOptions
    cl <- stPersistentOptions . stPersistentState <$> getTCState
    return $ cl{ optPragmaOptions = p }

class ( Applicative m
      , MonadTCEnv m
      , ReadTCState m
      , HasOptions m
      ) => MonadReduce m where
  liftReduce :: ReduceM a -> m a

  default liftReduce :: (MonadTrans t, MonadReduce n, t n ~ m) => ReduceM a -> m a
  liftReduce = lift . liftReduce

instance MonadReduce ReduceM where
  liftReduce = id

instance MonadReduce m => MonadReduce (ChangeT m)
instance MonadReduce m => MonadReduce (ExceptT err m)
instance MonadReduce m => MonadReduce (IdentityT m)
instance MonadReduce m => MonadReduce (ListT m)
instance MonadReduce m => MonadReduce (MaybeT m)
instance MonadReduce m => MonadReduce (ReaderT r m)
instance MonadReduce m => MonadReduce (StateT w m)
instance (Monoid w, MonadReduce m) => MonadReduce (WriterT w m)
instance MonadReduce m => MonadReduce (BlockT m)

---------------------------------------------------------------------------
-- * Monad with read-only 'TCEnv'
---------------------------------------------------------------------------

-- | @MonadTCEnv@ made into its own dedicated service class.
--   This allows us to use 'MonadReader' for 'ReaderT' extensions of @TCM@.
class Monad m => MonadTCEnv m where
  askTC   :: m TCEnv
  localTC :: (TCEnv -> TCEnv) -> m a -> m a

  default askTC :: (MonadTrans t, MonadTCEnv n, t n ~ m) => m TCEnv
  askTC = lift askTC

  default localTC
    :: (MonadTransControl t, MonadTCEnv n, t n ~ m)
    =>  (TCEnv -> TCEnv) -> m a -> m a
  localTC = liftThrough . localTC

instance MonadTCEnv m => MonadTCEnv (ChangeT m)
instance MonadTCEnv m => MonadTCEnv (ExceptT err m)
instance MonadTCEnv m => MonadTCEnv (IdentityT m)
instance MonadTCEnv m => MonadTCEnv (MaybeT m)
instance MonadTCEnv m => MonadTCEnv (ReaderT r m)
instance MonadTCEnv m => MonadTCEnv (StateT s m)
instance (Monoid w, MonadTCEnv m) => MonadTCEnv (WriterT w m)

instance MonadTCEnv m => MonadTCEnv (ListT m) where
  localTC = mapListT . localTC

{-# INLINE asksTC #-}
asksTC :: MonadTCEnv m => (TCEnv -> a) -> m a
asksTC f = f <$> askTC

{-# INLINE viewTC #-}
viewTC :: MonadTCEnv m => Lens' TCEnv a -> m a
viewTC l = asksTC (^. l)

{-# INLINE locallyTC #-}
-- | Modify the lens-indicated part of the @TCEnv@ in a subcomputation.
locallyTC :: MonadTCEnv m => Lens' TCEnv a -> (a -> a) -> m b -> m b
locallyTC l = localTC . over l

---------------------------------------------------------------------------
-- * Monad with mutable 'TCState'
---------------------------------------------------------------------------

-- | @MonadTCState@ made into its own dedicated service class.
--   This allows us to use 'MonadState' for 'StateT' extensions of @TCM@.
class Monad m => MonadTCState m where
  getTC :: m TCState
  putTC :: TCState -> m ()
  modifyTC :: (TCState -> TCState) -> m ()

  default getTC :: (MonadTrans t, MonadTCState n, t n ~ m) => m TCState
  getTC = lift getTC

  default putTC :: (MonadTrans t, MonadTCState n, t n ~ m) => TCState -> m ()
  putTC = lift . putTC

  default modifyTC :: (MonadTrans t, MonadTCState n, t n ~ m) => (TCState -> TCState) -> m ()
  modifyTC = lift . modifyTC

instance MonadTCState m => MonadTCState (MaybeT m)
instance MonadTCState m => MonadTCState (ListT m)
instance MonadTCState m => MonadTCState (ExceptT err m)
instance MonadTCState m => MonadTCState (ReaderT r m)
instance MonadTCState m => MonadTCState (StateT s m)
instance MonadTCState m => MonadTCState (ChangeT m)
instance MonadTCState m => MonadTCState (IdentityT m)
instance (Monoid w, MonadTCState m) => MonadTCState (WriterT w m)

{-# INLINE getsTC #-}
-- ** @TCState@ accessors (no lenses)
getsTC :: ReadTCState m => (TCState -> a) -> m a
getsTC f = f <$> getTCState

{-# INLINE modifyTC' #-}
-- | A variant of 'modifyTC' in which the computation is strict in the
-- new state.
modifyTC' :: MonadTCState m => (TCState -> TCState) -> m ()
modifyTC' f = do
  s' <- getTC
  putTC $! f s'

-- SEE TC.Monad.State
-- -- | Restore the 'TCState' after computation.
-- localTCState :: MonadTCState m => m a -> m a
-- localTCState = bracket_ getTC putTC

-- ** @TCState@ accessors via lenses

{-# INLINE useTC #-}
useTC :: ReadTCState m => Lens' TCState a -> m a
useTC l = do
  !x <- getsTC (^. l)
  return x

infix 4 `setTCLens`

{-# INLINE setTCLens #-}
-- | Overwrite the part of the 'TCState' focused on by the lens.
setTCLens :: MonadTCState m => Lens' TCState a -> a -> m ()
setTCLens l = modifyTC . set l

{-# INLINE setTCLens' #-}
-- | Overwrite the part of the 'TCState' focused on by the lens
-- (strictly).
setTCLens' :: MonadTCState m => Lens' TCState a -> a -> m ()
setTCLens' l = modifyTC' . set l

{-# INLINE modifyTCLens #-}
-- | Modify the part of the 'TCState' focused on by the lens.
modifyTCLens :: MonadTCState m => Lens' TCState a -> (a -> a) -> m ()
modifyTCLens l = modifyTC . over l

{-# INLINE modifyTCLens' #-}
-- | Modify the part of the 'TCState' focused on by the lens
-- (strictly).
modifyTCLens' :: MonadTCState m => Lens' TCState a -> (a -> a) -> m ()
modifyTCLens' l = modifyTC' . over l

{-# INLINE modifyTCLensM #-}
-- | Modify a part of the state monadically.
modifyTCLensM :: MonadTCState m => Lens' TCState a -> (a -> m a) -> m ()
modifyTCLensM l f = putTC =<< l f =<< getTC

{-# INLINE stateTCLens #-}
-- | Modify the part of the 'TCState' focused on by the lens, and return some result.
stateTCLens :: MonadTCState m => Lens' TCState a -> (a -> (r , a)) -> m r
stateTCLens l f = stateTCLensM l $ return . f

{-# INLINE stateTCLensM #-}
-- | Modify a part of the state monadically, and return some result.
stateTCLensM :: MonadTCState m => Lens' TCState a -> (a -> m (r , a)) -> m r
stateTCLensM l f = do
  s <- getTC
  (result , x) <- f $ s ^. l
  putTC $ set l x s
  return result


---------------------------------------------------------------------------
-- ** Monad with capability to block a computation
---------------------------------------------------------------------------

class Monad m => MonadBlock m where

  -- | `patternViolation b` aborts the current computation
  patternViolation :: Blocker -> m a

  default patternViolation :: (MonadTrans t, MonadBlock n, m ~ t n) => Blocker -> m a
  patternViolation = lift . patternViolation

  -- | `catchPatternErr handle m` runs m, handling pattern violations
  --    with `handle` (doesn't roll back the state)
  catchPatternErr :: (Blocker -> m a) -> m a -> m a

newtype BlockT m a = BlockT { unBlockT :: ExceptT Blocker m a }
  deriving ( Functor, Applicative, Monad, MonadTrans -- , MonadTransControl -- requires GHC >= 8.2
           , MonadIO, Fail.MonadFail
           , ReadTCState, HasOptions
           , MonadTCEnv, MonadTCState, MonadTCM
           )

instance Monad m => MonadBlock (BlockT m) where
  patternViolation = BlockT . throwError
  catchPatternErr h f = BlockT $ catchError (unBlockT f) (unBlockT . h)

instance Monad m => MonadBlock (ExceptT TCErr m) where
  patternViolation = throwError . PatternErr
  catchPatternErr h f = catchError f $ \case
    PatternErr b -> h b
    err          -> throwError err

runBlocked :: Monad m => BlockT m a -> m (Either Blocker a)
runBlocked = runExceptT . unBlockT
{-# INLINE runBlocked #-}

instance MonadBlock m => MonadBlock (MaybeT m) where
  catchPatternErr h m = MaybeT $ catchPatternErr (runMaybeT . h) $ runMaybeT m

instance MonadBlock m => MonadBlock (ReaderT e m) where
  catchPatternErr h m = ReaderT $ \ e ->
    let run = flip runReaderT e in catchPatternErr (run . h) (run m)

---------------------------------------------------------------------------
-- * Type checking monad transformer
---------------------------------------------------------------------------

-- | The type checking monad transformer.
-- Adds readonly 'TCEnv' and mutable 'TCState'.
newtype TCMT m a = TCM { unTCM :: IORef TCState -> TCEnv -> m a }

-- | Type checking monad.
type TCM = TCMT IO

{-# SPECIALIZE INLINE mapTCMT :: (forall a. IO a -> IO a) -> TCM a -> TCM a #-}
mapTCMT :: (forall a. m a -> n a) -> TCMT m a -> TCMT n a
mapTCMT f (TCM m) = TCM $ \ s e -> f (m s e)

pureTCM :: MonadIO m => (TCState -> TCEnv -> a) -> TCMT m a
pureTCM f = TCM $ \ r e -> do
  s <- liftIO $ readIORef r
  return (f s e)
{-# INLINE pureTCM #-}

-- One goal of the definitions and pragmas below is to inline the
-- monad operations as much as possible. This doesn't seem to have a
-- large effect on the performance of the normal executable, but (at
-- least on one machine/configuration) it has a massive effect on the
-- performance of the profiling executable [1], and reduces the time
-- attributed to bind from over 90% to about 25%.
--
-- [1] When compiled with -auto-all and run with -p: roughly 750%
-- faster for one example.

returnTCMT :: Applicative m => a -> TCMT m a
returnTCMT = \x -> TCM $ \_ _ -> pure x
{-# INLINE returnTCMT #-}

bindTCMT :: Monad m => TCMT m a -> (a -> TCMT m b) -> TCMT m b
bindTCMT = \(TCM m) k -> TCM $ \r e -> m r e >>= \x -> unTCM (k x) r e
{-# INLINE bindTCMT #-}

thenTCMT :: Applicative m => TCMT m a -> TCMT m b -> TCMT m b
thenTCMT = \(TCM m1) (TCM m2) -> TCM $ \r e -> m1 r e *> m2 r e
{-# INLINE thenTCMT #-}

instance Functor m => Functor (TCMT m) where
  fmap = fmapTCMT; {-# INLINE fmap #-}

fmapTCMT :: Functor m => (a -> b) -> TCMT m a -> TCMT m b
fmapTCMT = \f (TCM m) -> TCM $ \r e -> fmap f (m r e)
{-# INLINE fmapTCMT #-}

instance Applicative m => Applicative (TCMT m) where
  pure  = returnTCMT; {-# INLINE pure #-}
  (<*>) = apTCMT; {-# INLINE (<*>) #-}

apTCMT :: Applicative m => TCMT m (a -> b) -> TCMT m a -> TCMT m b
apTCMT = \(TCM mf) (TCM m) -> TCM $ \r e -> mf r e <*> m r e
{-# INLINE apTCMT #-}

instance MonadTrans TCMT where
    lift m = TCM $ \_ _ -> m; {-# INLINE lift #-}

-- We want a special monad implementation of fail.
-- Andreas, 2022-02-02, issue #5659:
-- @transformers-0.6@ requires exactly a @Monad@ superclass constraint here
-- if we want @instance MonadTrans TCMT@.
instance Monad m => Monad (TCMT m) where
    return = pure; {-# INLINE return #-}
    (>>=)  = bindTCMT; {-# INLINE (>>=) #-}
    (>>)   = (*>); {-# INLINE (>>) #-}

instance MonadIO m => Fail.MonadFail (TCMT m) where
  fail = internalError

instance MonadIO m => MonadIO (TCMT m) where
  liftIO m = TCM $ \ s env -> do
    liftIO $ wrap s (envRange env) $ do
      x <- m
      x `seq` return x
    where
      wrap s r m = E.catch m $ \ err -> do
        s <- readIORef s
        E.throwIO $ IOException s r err

instance ( MonadFix m
         ) => MonadFix (TCMT m) where
  mfix f = TCM $ \s env -> mdo
    x <- unTCM (f x) s env
    return x

instance MonadIO m => MonadTCEnv (TCMT m) where
  askTC             = TCM $ \ _ e -> return e; {-# INLINE askTC #-}
  localTC f (TCM m) = TCM $ \ s e -> m s (f e); {-# INLINE localTC #-}

instance MonadIO m => MonadTCState (TCMT m) where
  getTC   = TCM $ \ r _e -> liftIO (readIORef r); {-# INLINE getTC #-}
  putTC s = TCM $ \ r _e -> liftIO (writeIORef r s); {-# INLINE putTC #-}
  modifyTC f = putTC . f =<< getTC; {-# INLINE modifyTC #-}

instance MonadIO m => ReadTCState (TCMT m) where
  getTCState = getTC; {-# INLINE getTCState #-}
  locallyTCState l f = bracket_ (useTC l <* modifyTCLens l f) (setTCLens l); {-# INLINE locallyTCState #-}

instance MonadBlock TCM where
  patternViolation b = throwError (PatternErr b)
  catchPatternErr handle v =
       catchError_ v $ \err ->
       case err of
            -- Not putting s (which should really be the what's already there) makes things go
            -- a lot slower (+20% total time on standard library). How is that possible??
            -- The problem is most likely that there are internal catchErrors which forgets the
            -- state. catchError should preserve the state on pattern violations.
           PatternErr u -> handle u
           _            -> throwError err


instance MonadError TCErr TCM where
  throwError = liftIO . E.throwIO
  catchError m h = TCM $ \ r e -> do  -- now we are in the IO monad
    oldState <- readIORef r
    unTCM m r e `E.catch` \err -> do
      -- Reset the state, but do not forget changes to the persistent
      -- component. Not for pattern violations.
      case err of
        PatternErr{} -> return ()
        _            ->
          liftIO $ do
            newState <- readIORef r
            writeIORef r $ oldState { stPersistentState = stPersistentState newState }
      unTCM (h err) r e

-- | Like 'catchError', but resets the state completely before running the handler.
--   This means it also loses changes to the 'stPersistentState'.
--
--   The intended use is to catch internal errors during debug printing.
--   In debug printing, we are not expecting state changes.
instance CatchImpossible TCM where
  catchImpossibleJust f m h = TCM $ \ r e -> do
    -- save the state
    s <- readIORef r
    catchImpossibleJust f (unTCM m r e) $ \ err -> do
      writeIORef r s
      unTCM (h err) r e

instance MonadIO m => MonadReduce (TCMT m) where
  liftReduce = liftTCM . runReduceM; {-# INLINE liftReduce #-}

instance (IsString a, MonadIO m) => IsString (TCMT m a) where
  fromString s = return (fromString s)

-- | Strict (non-shortcut) semigroup.
--
--   Note that there might be a lazy alternative, e.g.,
--   for TCM All we might want 'Agda.Utils.Monad.and2M' as concatenation,
--   to shortcut conjunction in case we already have 'False'.
--
instance {-# OVERLAPPABLE #-} (MonadIO m, Semigroup a) => Semigroup (TCMT m a) where
  (<>) = liftA2 (<>)

-- | Strict (non-shortcut) monoid.
instance {-# OVERLAPPABLE #-} (MonadIO m, Semigroup a, Monoid a) => Monoid (TCMT m a) where
  mempty  = pure mempty
  mappend = (<>)
  mconcat = mconcat <.> sequence

instance {-# OVERLAPPABLE #-} (MonadIO m, Null a) => Null (TCMT m a) where
  empty = return empty
  null  = __IMPOSSIBLE__

-- | Preserve the state of the failing computation.
catchError_ :: TCM a -> (TCErr -> TCM a) -> TCM a
catchError_ m h = TCM $ \r e ->
  unTCM m r e
  `E.catch` \err -> unTCM (h err) r e

-- | Execute a finalizer even when an exception is thrown.
--   Does not catch any errors.
--   In case both the regular computation and the finalizer
--   throw an exception, the one of the finalizer is propagated.
finally_ :: TCM a -> TCM b -> TCM a
finally_ m f = do
    x <- m `catchError_` \ err -> f >> throwError err
    _ <- f
    return x

-- | Embedding a TCM computation.

class ( Applicative tcm, MonadIO tcm
      , MonadTCEnv tcm
      , MonadTCState tcm
      , HasOptions tcm
      ) => MonadTCM tcm where
    liftTCM :: TCM a -> tcm a

    default liftTCM :: (MonadTCM m, MonadTrans t, tcm ~ t m) => TCM a -> tcm a
    liftTCM = lift . liftTCM
    {-# INLINE liftTCM #-}

{-# RULES "liftTCM/id" liftTCM = id #-}
instance MonadIO m => MonadTCM (TCMT m) where
    liftTCM = mapTCMT liftIO
    {-# INLINE liftTCM #-}

instance MonadTCM tcm => MonadTCM (ChangeT tcm)
instance MonadTCM tcm => MonadTCM (ExceptT err tcm)
instance MonadTCM tcm => MonadTCM (IdentityT tcm)
instance MonadTCM tcm => MonadTCM (ListT tcm)
instance MonadTCM tcm => MonadTCM (MaybeT tcm)
instance MonadTCM tcm => MonadTCM (ReaderT r tcm)
instance MonadTCM tcm => MonadTCM (StateT s tcm)
instance (Monoid w, MonadTCM tcm) => MonadTCM (WriterT w tcm)

-- | We store benchmark statistics in an IORef.
--   This enables benchmarking pure computation, see
--   "Agda.Benchmarking".
instance MonadBench TCM where
  type BenchPhase TCM = Phase
  getBenchmark = liftIO $ getBenchmark
  putBenchmark = liftIO . putBenchmark
  finally = finally_

instance Null (TCM Doc) where
  empty = return empty
  null = __IMPOSSIBLE__

internalError :: (HasCallStack, MonadTCM tcm) => String -> tcm a
internalError s = withCallerCallStack $ \ loc ->
  liftTCM $ typeError' loc $ InternalError s

-- | The constraints needed for 'typeError' and similar.
type MonadTCError m = (MonadTCEnv m, ReadTCState m, MonadError TCErr m)

-- | Utility function for 1-arg constructed type errors.
-- Note that the @HasCallStack@ constraint is on the *resulting* function.
locatedTypeError :: MonadTCError m => (a -> TypeError) -> (HasCallStack => a -> m b)
locatedTypeError f e = withCallerCallStack (flip typeError' (f e))

genericError :: (HasCallStack, MonadTCError m) => String -> m a
genericError = locatedTypeError GenericError

{-# SPECIALIZE genericDocError :: Doc -> TCM a #-}
genericDocError :: (HasCallStack, MonadTCError m) => Doc -> m a
genericDocError = locatedTypeError GenericDocError

{-# SPECIALIZE typeError' :: CallStack -> TypeError -> TCM a #-}
typeError' :: MonadTCError m => CallStack -> TypeError -> m a
typeError' loc err = throwError =<< typeError'_ loc err

{-# SPECIALIZE typeError :: HasCallStack => TypeError -> TCM a #-}
typeError :: (HasCallStack, MonadTCError m) => TypeError -> m a
typeError err = withCallerCallStack $ \loc -> throwError =<< typeError'_ loc err

{-# SPECIALIZE typeError'_ :: CallStack -> TypeError -> TCM TCErr #-}
typeError'_ :: (MonadTCEnv m, ReadTCState m) => CallStack -> TypeError -> m TCErr
typeError'_ loc err = TypeError loc <$> getTCState <*> buildClosure err

{-# SPECIALIZE typeError_ :: HasCallStack => TypeError -> TCM TCErr #-}
typeError_ :: (HasCallStack, MonadTCEnv m, ReadTCState m) => TypeError -> m TCErr
typeError_ = withCallerCallStack . flip typeError'_

-- | Running the type checking monad (most general form).
{-# SPECIALIZE runTCM :: TCEnv -> TCState -> TCM a -> IO (a, TCState) #-}
runTCM :: MonadIO m => TCEnv -> TCState -> TCMT m a -> m (a, TCState)
runTCM e s m = do
  r <- liftIO $ newIORef s
  a <- unTCM m r e
  s <- liftIO $ readIORef r
  return (a, s)

-- | Running the type checking monad on toplevel (with initial state).
runTCMTop :: TCM a -> IO (Either TCErr a)
runTCMTop m = (Right <$> runTCMTop' m) `E.catch` (return . Left)

runTCMTop' :: MonadIO m => TCMT m a -> m a
runTCMTop' m = do
  r <- liftIO $ newIORef initState
  unTCM m r initEnv

-- | 'runSafeTCM' runs a safe 'TCM' action (a 'TCM' action which
--   cannot fail, except that it might raise 'IOException's) in the
--   initial environment.

runSafeTCM :: TCM a -> TCState -> IO (a, TCState)
runSafeTCM m st =
  runTCM initEnv st m `E.catch` \(e :: TCErr) -> case e of
    IOException _ _ err -> E.throwIO err
    _                   -> __IMPOSSIBLE__

-- | Runs the given computation in a separate thread, with /a copy/ of
-- the current state and environment.
--
-- Note that Agda sometimes uses actual, mutable state. If the
-- computation given to @forkTCM@ tries to /modify/ this state, then
-- bad things can happen, because accesses are not mutually exclusive.
-- The @forkTCM@ function has been added mainly to allow the thread to
-- /read/ (a snapshot of) the current state in a convenient way.
--
-- Note also that exceptions which are raised in the thread are not
-- propagated to the parent, so the thread should not do anything
-- important.

forkTCM :: TCM a -> TCM ()
forkTCM m = do
  s <- getTC
  e <- askTC
  liftIO $ void $ C.forkIO $ void $ runTCM e s m

---------------------------------------------------------------------------
-- * Interaction Callback
---------------------------------------------------------------------------

-- | Callback fuction to call when there is a response
--   to give to the interactive frontend.
--
--   Note that the response is given in pieces and incrementally,
--   so the user can have timely response even during long computations.
--
--   Typical 'InteractionOutputCallback' functions:
--
--    * Convert the response into a 'String' representation and
--      print it on standard output
--      (suitable for inter-process communication).
--
--    * Put the response into a mutable variable stored in the
--      closure of the 'InteractionOutputCallback' function.
--      (suitable for intra-process communication).

type InteractionOutputCallback = Response_boot TCErr TCWarning WarningsAndNonFatalErrors -> TCM ()

-- | The default 'InteractionOutputCallback' function prints certain
-- things to stdout (other things generate internal errors).

defaultInteractionOutputCallback :: InteractionOutputCallback
defaultInteractionOutputCallback = \case
  Resp_HighlightingInfo {}  -> __IMPOSSIBLE__
  Resp_Status {}            -> __IMPOSSIBLE__
  Resp_JumpToError {}       -> __IMPOSSIBLE__
  Resp_InteractionPoints {} -> __IMPOSSIBLE__
  Resp_GiveAction {}        -> __IMPOSSIBLE__
  Resp_MakeCase {}          -> __IMPOSSIBLE__
  Resp_SolveAll {}          -> __IMPOSSIBLE__
  Resp_DisplayInfo {}       -> __IMPOSSIBLE__
  Resp_RunningInfo _ s      -> liftIO $ do
                                 putStr s
                                 hFlush stdout
  Resp_ClearRunningInfo {}  -> __IMPOSSIBLE__
  Resp_ClearHighlighting {} -> __IMPOSSIBLE__
  Resp_DoneAborting {}      -> __IMPOSSIBLE__
  Resp_DoneExiting {}       -> __IMPOSSIBLE__

---------------------------------------------------------------------------
-- * Names for generated definitions
---------------------------------------------------------------------------

-- | Base name for patterns in telescopes
patternInTeleName :: String
patternInTeleName = ".patternInTele"

-- | Base name for extended lambda patterns
extendedLambdaName :: String
extendedLambdaName = ".extendedlambda"

-- | Check whether we have an definition from an extended lambda.
isExtendedLambdaName :: A.QName -> Bool
isExtendedLambdaName = (extendedLambdaName `List.isPrefixOf`) . prettyShow . nameConcrete . qnameName

-- | Name of absurdLambda definitions.
absurdLambdaName :: String
absurdLambdaName = ".absurdlambda"

-- | Check whether we have an definition from an absurd lambda.
isAbsurdLambdaName :: QName -> Bool
isAbsurdLambdaName = (absurdLambdaName ==) . prettyShow . qnameName

-- | Base name for generalized variable projections
generalizedFieldName :: String
generalizedFieldName = ".generalizedField-"

-- | Check whether we have a generalized variable field
getGeneralizedFieldName :: A.QName -> Maybe String
getGeneralizedFieldName q
  | generalizedFieldName `List.isPrefixOf` strName = Just (drop (length generalizedFieldName) strName)
  | otherwise                                      = Nothing
  where strName = prettyShow $ nameConcrete $ qnameName q

---------------------------------------------------------------------------
-- * KillRange instances
---------------------------------------------------------------------------

instance KillRange Signature where
  killRange (Sig secs defs rews) = killRangeN Sig secs defs rews

instance KillRange Sections where
  killRange = fmap killRange

instance KillRange Definitions where
  killRange = fmap killRange

instance KillRange RewriteRuleMap where
  killRange = fmap killRange

instance KillRange Section where
  killRange (Section tel) = killRangeN Section tel

instance KillRange Definition where
  killRange (Defn ai name t st pols occs gens gpars displ mut compiled inst copy ma nc inj copat blk lang def) =
    killRangeN Defn ai name t st pols occs gens gpars displ mut compiled inst copy ma nc inj copat blk lang def
    -- TODO clarify: Keep the range in the defName field?

instance KillRange NumGeneralizableArgs where
  killRange = id

instance KillRange NLPat where
  killRange (PVar x y) = killRangeN PVar x y
  killRange (PDef x y) = killRangeN PDef x y
  killRange (PLam x y) = killRangeN PLam x y
  killRange (PPi x y)  = killRangeN PPi x y
  killRange (PSort x)  = killRangeN PSort x
  killRange (PBoundVar x y) = killRangeN PBoundVar x y
  killRange (PTerm x)  = killRangeN PTerm x

instance KillRange NLPType where
  killRange (NLPType s a) = killRangeN NLPType s a

instance KillRange NLPSort where
  killRange (PUniv u l) = killRangeN (PUniv u) l
  killRange s@(PInf f n) = s
  killRange PSizeUniv = PSizeUniv
  killRange PLockUniv = PLockUniv
  killRange PLevelUniv = PLevelUniv
  killRange PIntervalUniv = PIntervalUniv

instance KillRange RewriteRule where
  killRange (RewriteRule q gamma f es rhs t c) =
    killRangeN RewriteRule q gamma f es rhs t c

instance KillRange CompiledRepresentation where
  killRange = id


instance KillRange EtaEquality where
  killRange = id

instance KillRange System where
  killRange (System tel sys) = System (killRange tel) (killRange sys)

instance KillRange ExtLamInfo where
  killRange (ExtLamInfo m b sys) = killRangeN ExtLamInfo m b sys

instance KillRange FunctionFlag where
  killRange = id

instance KillRange CompKit where
  killRange = id

instance KillRange ProjectionLikenessMissing where
  killRange = id

instance KillRange BuiltinSort where
  killRange = id

instance KillRange Defn where
  killRange def =
    case def of
      Axiom a -> Axiom a
      DataOrRecSig n -> DataOrRecSig n
      GeneralizableVar -> GeneralizableVar
      AbstractDefn{} -> __IMPOSSIBLE__ -- only returned by 'getConstInfo'!
      Function a b c d e f g h i j k l m n o p ->
        killRangeN Function a b c d e f g h i j k l m n o p
      Datatype a b c d e f g h i j   -> killRangeN Datatype a b c d e f g h i j
      Record a b c d e f g h i j k l m -> killRangeN Record a b c d e f g h i j k l m
      Constructor a b c d e f g h i j k -> killRangeN Constructor a b c d e f g h i j k
      Primitive a b c d e f          -> killRangeN Primitive a b c d e f
      PrimitiveSort a b              -> killRangeN PrimitiveSort a b

instance KillRange MutualId where
  killRange = id

instance KillRange c => KillRange (FunctionInverse' c) where
  killRange NotInjective = NotInjective
  killRange (Inverse m)  = Inverse $ killRangeMap m

instance KillRange TermHead where
  killRange SortHead     = SortHead
  killRange PiHead       = PiHead
  killRange (ConsHead q) = ConsHead $ killRange q
  killRange h@VarHead{}  = h
  killRange UnknownHead  = UnknownHead

instance KillRange Projection where
  killRange (Projection a b c d e) = killRangeN Projection a b c d e

instance KillRange ProjLams where
  killRange = id

instance KillRange a => KillRange (Open a) where
  killRange = fmap killRange

instance KillRange DisplayForm where
  killRange (Display n es dt) = killRangeN Display n es dt

instance KillRange Polarity where
  killRange = id

instance KillRange IsForced where
  killRange = id

instance KillRange DoGeneralize where
  killRange = id

instance KillRange DisplayTerm where
  killRange dt =
    case dt of
      DWithApp dt dts es -> killRangeN DWithApp dt dts es
      DCon q ci dts      -> killRangeN DCon q ci dts
      DDef q dts         -> killRangeN DDef q dts
      DDot' v es         -> killRangeN DDot' v es
      DTerm' v es        -> killRangeN DTerm' v es

instance KillRange a => KillRange (Closure a) where
  killRange = id

---------------------------------------------------------------------------
-- NFData instances
---------------------------------------------------------------------------

instance NFData NumGeneralizableArgs where
  rnf NoGeneralizableArgs       = ()
  rnf (SomeGeneralizableArgs _) = ()

instance NFData TCErr where
  rnf (TypeError a b c)   = rnf a `seq` rnf b `seq` rnf c
  rnf (Exception a b)     = rnf a `seq` rnf b
  rnf (IOException a b c) = rnf a `seq` rnf b `seq` rnf (c == c)
                            -- At the time of writing there is no
                            -- NFData instance for E.IOException.
  rnf (PatternErr a)      = rnf a

-- | This instance could be optimised, some things are guaranteed to
-- be forced.

instance NFData PreScopeState

-- | This instance could be optimised, some things are guaranteed to
-- be forced.

instance NFData PostScopeState

instance NFData TCState
instance NFData DisambiguatedName
instance NFData MutualBlock
instance NFData OpaqueBlock
instance NFData (BiMap RawTopLevelModuleName ModuleNameHash)
instance NFData PersistentTCState
instance NFData LoadedFileCache
instance NFData TypeCheckAction
instance NFData ModuleCheckMode
instance NFData ModuleInfo
instance NFData ForeignCode
instance NFData Interface
instance NFData a => NFData (Closure a)
instance NFData ProblemConstraint
instance NFData WhyCheckModality
instance NFData Constraint
instance NFData Signature
instance NFData Comparison
instance NFData CompareAs
instance NFData a => NFData (Open a)
instance NFData a => NFData (Judgement a)
instance NFData DoGeneralize
instance NFData GeneralizedValue
instance NFData MetaVariable
instance NFData Listener
instance NFData MetaInstantiation
instance NFData Instantiation
instance NFData RemoteMetaVariable
instance NFData Frozen
instance NFData PrincipalArgTypeMetas
instance NFData TypeCheckingProblem
instance NFData RunMetaOccursCheck
instance NFData MetaInfo
instance NFData InteractionPoint
instance NFData InteractionPoints
instance NFData Overapplied
instance NFData t => NFData (IPBoundary' t)
instance NFData IPClause
instance NFData DisplayForm
instance NFData DisplayTerm
instance NFData NLPat
instance NFData NLPType
instance NFData NLPSort
instance NFData RewriteRule
instance NFData Definition
instance NFData Polarity
instance NFData IsForced
instance NFData Projection
instance NFData ProjLams
instance NFData CompilerPragma
instance NFData System
instance NFData ExtLamInfo
instance NFData EtaEquality
instance NFData FunctionFlag
instance NFData CompKit
instance NFData AxiomData
instance NFData DataOrRecSigData
instance NFData ProjectionLikenessMissing
instance NFData FunctionData
instance NFData DatatypeData
instance NFData RecordData
instance NFData ConstructorData
instance NFData PrimitiveData
instance NFData PrimitiveSortData
instance NFData Defn
instance NFData Simplification
instance NFData AllowedReduction
instance NFData ReduceDefs
instance NFData PrimFun
instance NFData c => NFData (FunctionInverse' c)
instance NFData TermHead
instance NFData Call
instance NFData BuiltinSort
instance NFData pf => NFData (Builtin pf)
instance NFData HighlightingLevel
instance NFData HighlightingMethod
instance NFData TCEnv
instance NFData LetBinding
instance NFData UnquoteFlags
instance NFData AbstractMode
instance NFData ExpandHidden
instance NFData CandidateKind
instance NFData Candidate
instance NFData Warning
instance NFData RecordFieldWarning
instance NFData TCWarning
instance NFData CallInfo
instance NFData TerminationError
instance NFData ErasedDatatypeReason
instance NFData SplitError
instance NFData NegativeUnification
instance NFData UnificationFailure
instance NFData UnquoteError
instance NFData TypeError
instance NFData LHSOrPatSyn
instance NFData DataOrRecordE
instance NFData InductionAndEta
instance NFData IllegalRewriteRuleReason
instance NFData IncorrectTypeForRewriteRelationReason
