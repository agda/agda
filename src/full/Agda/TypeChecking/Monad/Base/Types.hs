-- | Data structures for the type checker.
--
-- Part of "Agda.TypeChecking.Monad.Base", extracted to avoid import cycles.

module Agda.TypeChecking.Monad.Base.Types where

import Data.Map                       ( Map )
import GHC.Generics                   ( Generic )

import Agda.Syntax.Info               ( MetaNameSuggestion )
import Agda.Syntax.Internal
import Agda.Syntax.TopLevelModuleName ( TopLevelModuleName )

import Agda.Utils.FileName            ( AbsolutePath )

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

-- | Maps top-level module names to the corresponding source file
-- names.

type ModuleToSource = Map TopLevelModuleName AbsolutePath

---------------------------------------------------------------------------
-- * Meta variables
---------------------------------------------------------------------------

-- | For printing, we couple a meta with its name suggestion.
data NamedMeta = NamedMeta
  { nmSuggestion :: MetaNameSuggestion
  , nmid         :: MetaId
  }

-- Feel free to move more types from Agda.TypeChecking.Monad.Base here when needed...
