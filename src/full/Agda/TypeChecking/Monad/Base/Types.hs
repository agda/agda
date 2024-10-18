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
import Data.Map                       ( Map )
import GHC.Generics                   ( Generic )

import Agda.Syntax.Info               ( MetaNameSuggestion )
import Agda.Syntax.Internal
import Agda.Syntax.TopLevelModuleName as X ( TopLevelModuleName )

import Agda.Utils.FileId              as X ( FileId, FileDictBuilder )
import Agda.Utils.FileName            as X ( AbsolutePath )
import Agda.Utils.Lens                ( Lens', (&&&), iso )
import Agda.Utils.Null                ( Null(..) )

---------------------------------------------------------------------------
-- * Context
---------------------------------------------------------------------------

-- | The @Context@ is a stack of 'ContextEntry's.
type Context      = [ContextEntry]
type ContextEntry = Dom (Name, Type)

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

-- | 'SourceFile's must exist and be registered in our file dictionary.

newtype SourceFile = SourceFile { srcFileId :: FileId }
  deriving (Eq, Ord, Show, Generic)

-- | Maps top-level module names to the corresponding source file ids.

type ModuleToSourceId = Map TopLevelModuleName SourceFile

data ModuleToSource = ModuleToSource
  { fileDict         :: FileDictBuilder
  , moduleToSourceId :: ModuleToSourceId
  }

lensPairModuleToSource :: Lens' (FileDictBuilder, ModuleToSourceId) ModuleToSource
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

instance Null ModuleToSource where
  empty = ModuleToSource empty empty
  null (ModuleToSource dict m2s) = null dict && null m2s

-- NFData instances

instance NFData SourceFile
