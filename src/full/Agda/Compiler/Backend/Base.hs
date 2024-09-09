{-# OPTIONS_GHC -Wunused-imports #-}

module Agda.Compiler.Backend.Base where

import Agda.Interaction.Options (ArgDescr(..), OptDescr(..), Flag)
import Agda.Syntax.Abstract.Name (QName)
import Agda.Syntax.Common (BackendName, IsMain)
import Agda.Syntax.TopLevelModuleName (TopLevelModuleName)
import {-# SOURCE #-} Agda.TypeChecking.Monad.Base (Definition)


import Control.DeepSeq (NFData, rnf)
import Data.Map (Map)
import Data.Text (Text)

import GHC.Generics (Generic)

type BackendVersion = Text

data Backend_boot tcm where
  Backend :: NFData opts => Backend'_boot tcm opts env menv mod def -> Backend_boot tcm

data Backend'_boot tcm opts env menv mod def = Backend'
  { backendName      :: BackendName
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
  , compileDef       :: env -> menv -> IsMain -> Definition -> tcm def
      -- ^ Compile a single definition.
  , scopeCheckingSuffices :: Bool
      -- ^ True if the backend works if @--only-scope-checking@ is used.
  , mayEraseType     :: QName -> tcm Bool
      -- ^ The treeless compiler may ask the Backend if elements
      --   of the given type maybe possibly erased.
      --   The answer should be 'False' if the compilation of the type
      --   is used by a third party, e.g. in a FFI binding.
  }
  deriving Generic

data Recompile menv mod = Recompile menv | Skip mod


instance NFData (Backend_boot tcm) where
  rnf (Backend b) = rnf b

instance NFData opts => NFData (Backend'_boot tcm opts env menv mod def) where
  rnf (Backend' a b c d e f g h i j k l) =
    rnf a `seq` rnf b `seq` rnf c `seq` rnf' d `seq` rnf e `seq`
    rnf f `seq` rnf g `seq` rnf h `seq` rnf i `seq` rnf j `seq`
    rnf k `seq` rnf l
    where
    rnf' []                   = ()
    rnf' (Option a b c d : e) =
      rnf a `seq` rnf b `seq` rnf'' c `seq` rnf d `seq` rnf' e

    rnf'' (NoArg a)    = rnf a
    rnf'' (ReqArg a b) = rnf a `seq` rnf b
    rnf'' (OptArg a b) = rnf a `seq` rnf b
