-- | Lenses for 'CommandLineOptions' and 'PragmaOptions'.
--
--   Add as needed.
--
--   Nothing smart happening here.

module Agda.Interaction.Options.Lenses where

import Control.Monad.State

import Agda.TypeChecking.Monad.Base
import Agda.TypeChecking.Monad.State
import Agda.Interaction.Options

---------------------------------------------------------------------------
-- * Pragma options
---------------------------------------------------------------------------

class LensPragmaOptions a where
  getPragmaOptions :: a -> PragmaOptions
  setPragmaOptions :: PragmaOptions -> a -> a
  mapPragmaOptions :: (PragmaOptions -> PragmaOptions) -> a -> a

  -- default implementations
  setPragmaOptions     = mapPragmaOptions . const
  mapPragmaOptions f a = setPragmaOptions (f $ getPragmaOptions a) a

instance LensPragmaOptions TCState where
  getPragmaOptions = stPragmaOptions
  setPragmaOptions opts st = st { stPragmaOptions = opts }

modifyPragmaOptions :: (PragmaOptions -> PragmaOptions) -> TCM ()
modifyPragmaOptions = modify . mapPragmaOptions

---------------------------------------------------------------------------
-- * Command line options
---------------------------------------------------------------------------

class LensCommandLineOptions a where
  getCommandLineOptions :: a -> CommandLineOptions
  setCommandLineOptions :: CommandLineOptions -> a -> a
  mapCommandLineOptions :: (CommandLineOptions -> CommandLineOptions) -> a -> a

  -- default implementations
  setCommandLineOptions     = mapCommandLineOptions . const
  mapCommandLineOptions f a = setCommandLineOptions (f $ getCommandLineOptions a) a

instance LensCommandLineOptions PersistentTCState where
  getCommandLineOptions = stPersistentOptions
  setCommandLineOptions opts st = st { stPersistentOptions = opts }

instance LensCommandLineOptions TCState where
  getCommandLineOptions = getCommandLineOptions . stPersistent
  mapCommandLineOptions = updatePersistentState . mapCommandLineOptions

modifyCommandLineOptions :: (CommandLineOptions -> CommandLineOptions) -> TCM ()
modifyCommandLineOptions = modify . mapCommandLineOptions

---------------------------------------------------------------------------
-- * Include directories
---------------------------------------------------------------------------

class LensIncludeDirs a where
  getIncludeDirs :: a -> IncludeDirs
  setIncludeDirs :: IncludeDirs -> a -> a
  mapIncludeDirs :: (IncludeDirs -> IncludeDirs) -> a -> a

  -- default implementations
  setIncludeDirs     = mapIncludeDirs . const
  mapIncludeDirs f a = setIncludeDirs (f $ getIncludeDirs a) a

instance LensIncludeDirs CommandLineOptions where
  getIncludeDirs = optIncludeDirs
  setIncludeDirs is opts = opts { optIncludeDirs = is }

instance LensIncludeDirs PersistentTCState where
  getIncludeDirs = getIncludeDirs . getCommandLineOptions
  mapIncludeDirs = mapCommandLineOptions . mapIncludeDirs

instance LensIncludeDirs TCState where
  getIncludeDirs = getIncludeDirs . getCommandLineOptions
  mapIncludeDirs = mapCommandLineOptions . mapIncludeDirs

{-
instance LensIncludeDirs TCState where
  getIncludeDirs = getIncludeDirs . stPersistent
  mapIncludeDirs = updatePersistentState mapIncludeDirs
-}

modifyIncludeDirs :: (IncludeDirs -> IncludeDirs) -> TCM ()
modifyIncludeDirs = modify . mapIncludeDirs

putIncludeDirs :: IncludeDirs -> TCM ()
putIncludeDirs = modify . setIncludeDirs
