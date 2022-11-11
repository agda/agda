-- | Data structures for the type checker.
--
-- Part of "Agda.TypeChecking.Monad.Base", extracted to avoid import cycles.

module Agda.TypeChecking.Monad.Base.Types
  ( module Agda.TypeChecking.Monad.Base.Types
  , module X
  )
where

import Prelude hiding (null)

import Control.DeepSeq                ( NFData )
import Data.EnumMap                   ( EnumMap )
import Data.Functor                   ( (<&>) )
import Data.Map                       ( Map )
import GHC.Generics                   ( Generic )

import Agda.Syntax.Info               ( MetaNameSuggestion )
import Agda.Syntax.Internal
import Agda.Syntax.TopLevelModuleName as X ( TopLevelModuleName )

import Agda.Utils.FileId              as X ( FileId, FileDictBuilder )
import Agda.Utils.FileName            as X ( AbsolutePath )
import Agda.Utils.Lens                ( Lens', (&&&), iso )
import Agda.Utils.Null                ( Null(..) )

import Agda.Syntax.Internal           ( Dom, Name, Type )
import Agda.Syntax.Common
  ( LensArgInfo(..), LensCohesion, LensHiding, LensModality, LensOrigin, LensQuantity, LensRelevance, LensModalPolarity )

---------------------------------------------------------------------------
-- * Context
---------------------------------------------------------------------------

-- | The @Context@ is a stack of 'ContextEntry's.
type Context = [ContextEntry]

data ContextEntry
  = CtxVar
    { ceName :: Name
    , ceType :: Dom Type
    }
  -- N.B. 2024-11-29 there might be CtxLet in the future.
  deriving (Show, Generic)

instance LensArgInfo ContextEntry where
  getArgInfo (CtxVar _ a) = getArgInfo a
  mapArgInfo f (CtxVar x a) = CtxVar x $ mapArgInfo f a

instance LensModality  ContextEntry
instance LensRelevance ContextEntry
instance LensCohesion  ContextEntry
instance LensOrigin    ContextEntry
instance LensQuantity  ContextEntry
instance LensHiding    ContextEntry
instance LensModalPolarity ContextEntry

---------------------------------------------------------------------------
-- * Conversion
---------------------------------------------------------------------------

data Comparison = CmpEq | CmpLeq
  deriving (Eq, Show, Generic)

-- | Polarity for equality and subtype checking.
data Polarity
  = Covariant      -- ^ monotone
  | Contravariant  -- ^ antitone
  | Invariant      -- ^ no information (mixed variance)
  | Nonvariant     -- ^ constant
  deriving (Show, Eq, Generic)

---------------------------------------------------------------------------
-- * Cubical
---------------------------------------------------------------------------

-- | Datatype representing a single boundary condition:
--   x_0 = u_0, ... ,x_n = u_n ⊢ t = ?n es
data IPFace' t = IPFace'
  { faceEqns :: [(t, t)]
  , faceRHS  :: t
  }

---------------------------------------------------------------------------
-- * Highlighting
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

---------------------------------------------------------------------------
-- * Managing file names
---------------------------------------------------------------------------

-- | Discern Agda's primitive modules from other file modules.
--   @IsPrimitiveModule `implies` IsBuiltinModuleWithSafePostulate `implies` isBuiltinModule.

--   Keep constructors in this order!
data IsBuiltinModule
  = IsPrimitiveModule
      -- ^ Very magical module, e.g. @Agda.Primitive@.
  | IsBuiltinModuleWithSafePostulates
      -- ^ Safe module, e.g. @Agda.Builtin.Equality@.
  | IsBuiltinModule
      -- ^ Any builtin module.
  deriving (Eq, Ord, Show, Generic)

-- | Collection of 'FileId's of primitive modules.

type BuiltinModuleIds = EnumMap FileId IsBuiltinModule

-- | Translation between 'AbsolutePath' and 'FileId' that also knows about Agda's builtin modules.

data FileDictWithBuiltins = FileDictWithBuiltins
  { fileDictBuilder  :: !FileDictBuilder
      -- ^ (Building a) translation between 'AbsolutePath' and 'FileId'.
  , builtinModuleIds :: !BuiltinModuleIds
      -- ^ For the known 'FileId's, remember whether they refer to Agda's builtin modules.
  , primitiveLibDir  :: !PrimitiveLibDir
      -- ^ The absolute path to the directory with the builtin modules.
      --   Needs to be set upon initialization.
  }
  deriving Generic

type PrimitiveLibDir = AbsolutePath

-- | 'SourceFile's must exist and be registered in our file dictionary.

newtype SourceFile = SourceFile { srcFileId :: FileId }
  deriving (Eq, Ord, Show, Generic)

-- | Maps top-level module names to the corresponding source file ids.

type ModuleToSourceId = Map TopLevelModuleName SourceFile

data ModuleToSource = ModuleToSource
  { fileDict         :: !FileDictWithBuiltins
  , moduleToSourceId :: !ModuleToSourceId
  }

-- ** Lenses

lensFileDictFileDictBuilder :: Lens' FileDictWithBuiltins FileDictBuilder
lensFileDictFileDictBuilder f s = f (fileDictBuilder s) <&> \ x -> s { fileDictBuilder = x }

lensFileDictBuiltinModuleIds :: Lens' FileDictWithBuiltins BuiltinModuleIds
lensFileDictBuiltinModuleIds f s = f (builtinModuleIds s) <&> \ x -> s { builtinModuleIds = x }

lensFileDictPrimitiveLibDir :: Lens' FileDictWithBuiltins PrimitiveLibDir
lensFileDictPrimitiveLibDir f s = f (primitiveLibDir s) <&> \ x -> s { primitiveLibDir = x }

lensPairModuleToSource :: Lens' (FileDictWithBuiltins, ModuleToSourceId) ModuleToSource
lensPairModuleToSource = iso (uncurry ModuleToSource) (fileDict &&& moduleToSourceId)

---------------------------------------------------------------------------
-- * Meta variables
---------------------------------------------------------------------------

-- | For printing, we couple a meta with its name suggestion.
data NamedMeta = NamedMeta
  { nmSuggestion :: MetaNameSuggestion
  , nmid         :: MetaId
  }



-- Feel free to move more types from Agda.TypeChecking.Monad.Base here when needed...

-- Null instances

-- Andreas, 2024-11-10: Let's not have these instances because there is no default primLibDir:
--
-- instance Null FileDictWithBuiltins where
--   empty = FileDictWithBuiltins empty empty __IMPOSSIBLE__
--   null (FileDictWithBuiltins a b _primLibDir) = null a && null b
--
-- instance Null ModuleToSource where
--   empty = ModuleToSource empty empty
--   null (ModuleToSource dict m2s) = null dict && null m2s

-- NFData instances

instance NFData ContextEntry
instance NFData FileDictWithBuiltins
instance NFData SourceFile
instance NFData IsBuiltinModule
