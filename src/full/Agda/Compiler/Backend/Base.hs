{-# OPTIONS_GHC -Wunused-imports #-}

module Agda.Compiler.Backend.Base where

import Control.DeepSeq (NFData, rnf)
import Data.Map (Map)
import Data.Text (Text)
import GHC.Generics (Generic)

import Agda.Syntax.Abstract.Name (QName)
import Agda.Syntax.Common (BackendName, IsMain, InteractionId)
import Agda.Syntax.TopLevelModuleName (TopLevelModuleName)
import Agda.Syntax.Position (Range)

import Agda.Interaction.Base (CommandM')
import Agda.Interaction.Options (OptDescr, Flag)

type BackendVersion = Text

data Backend_boot definition tcm where
  Backend :: NFData opts => Backend'_boot definition tcm opts env menv mod def -> Backend_boot definition tcm

data Backend'_boot definition tcm opts env menv mod def = Backend'
  { backendName      :: BackendName
      -- ^ the name of the backend
  , backendVersion   :: Maybe BackendVersion
      -- ^ Optional version information to be printed with @--version@.
  , options          :: opts
      -- ^ Default options
  , commandLineFlags :: [OptDescr (Flag opts)]
      -- ^ Backend-specific command-line flags. Should at minimum contain a
      --   flag to enable the backend.
  , isEnabled        :: opts -> Bool
      -- ^ Unless the backend has been enabled, @runAgda@ will fall back to
      --   vanilla Agda behaviour.
  , preCompile       :: opts -> tcm env
      -- ^ Called after type checking completes, but before compilation starts.
  , postCompile      :: env -> IsMain -> Map TopLevelModuleName mod ->
                        tcm ()
      -- ^ Called after module compilation has completed. The @IsMain@ argument
      --   is @NotMain@ if the @--no-main@ flag is present.
  , preModule        :: env -> IsMain -> TopLevelModuleName ->
                        Maybe FilePath -> tcm (Recompile menv mod)
      -- ^ Called before compilation of each module. Gets the path to the
      --   @.agdai@ file to allow up-to-date checking of previously written
      --   compilation results. Should return @Skip m@ if compilation is not
      --   required. Will be @Nothing@ if only scope checking.
  , postModule       :: env -> menv -> IsMain -> TopLevelModuleName ->
                        [def] -> tcm mod
      -- ^ Called after all definitions of a module have been compiled.
  , compileDef       :: env -> menv -> IsMain -> definition -> tcm def
      -- ^ Compile a single definition.
  , scopeCheckingSuffices :: Bool
      -- ^ True if the backend works if @--only-scope-checking@ is used.
  , mayEraseType     :: QName -> tcm Bool
      -- ^ The treeless compiler may ask the Backend if elements
      --   of the given type maybe possibly erased.
      --   The answer should be 'False' if the compilation of the type
      --   is used by a third party, e.g. in a FFI binding.
  , backendInteractTop  :: Maybe (BackendCommandTop tcm)
      -- ^ Backend-specific top-level interactive command.
  , backendInteractHole :: Maybe (BackendCommandHole tcm)
      -- ^ Backend-specific hole-level interactive command.
  }
  deriving Generic

data Recompile menv mod = Recompile menv | Skip mod

-- | For the sake of flexibility, we parametrize interactive commands with an
-- arbitrary string payload, e.g. to allow extra user input, or have backends
-- provide multiple commands with a single record field.
type CommandPayload = String

-- | The type of top-level backend interactive commmands.
type BackendCommandTop tcm
   = CommandPayload -- ^ arbitrary user payload
  -> CommandM' tcm ()

-- | The type of top-level backend interactive commmands.
type BackendCommandHole tcm
   = CommandPayload -- ^ arbitrary user payload
  -> InteractionId  -- ^ the hole's ID
  -> Range          -- ^ the hole's range
  -> String         -- ^ the hole's contents
  -> CommandM' tcm ()

instance NFData (Backend_boot definition tcm) where
  rnf (Backend b) = rnf b

instance NFData opts => NFData (Backend'_boot definition tcm opts env menv mod def) where
  rnf (Backend' a b c d e f g h i j k l !m !n) =
    rnf a `seq`
    rnf b `seq`
    rnf c `seq`
    -- Andreas, 2025-07-31, cannot normalize functions with deepseq-1.5.2.0 (GHC 9.10.3).
    -- see https://github.com/haskell/deepseq/issues/111.
    -- rnf d `seq`
    -- rnf e `seq`
    -- rnf f `seq`
    -- rnf g `seq`
    -- rnf h `seq`
    -- rnf i `seq`
    -- rnf j `seq`
    rnf k `seq`
    -- rnf l `seq`
    -- rnf m `seq`
    -- rnf n `seq`
    ()
