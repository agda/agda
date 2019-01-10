-- | Lenses for 'CommandLineOptions' and 'PragmaOptions'.
--
--   Add as needed.
--
--   Nothing smart happening here.

module Agda.Interaction.Options.Lenses where

import Control.Monad.State

import System.FilePath ((</>))

import Agda.TypeChecking.Monad.Base
import Agda.TypeChecking.Monad.State
import Agda.Interaction.Options

import Agda.Utils.Lens
import Agda.Utils.FileName

---------------------------------------------------------------------------
-- * Pragma options
---------------------------------------------------------------------------

class LensPragmaOptions a where
  getPragmaOptions  :: a -> PragmaOptions
  setPragmaOptions  :: PragmaOptions -> a -> a
  mapPragmaOptions  :: (PragmaOptions -> PragmaOptions) -> a -> a
  lensPragmaOptions :: Lens' PragmaOptions a
  -- lensPragmaOptions :: forall f. Functor f => (PragmaOptions -> f PragmaOptions) -> a -> f a

  -- default implementations
  setPragmaOptions     = mapPragmaOptions . const
  mapPragmaOptions f a = setPragmaOptions (f $ getPragmaOptions a) a

instance LensPragmaOptions CommandLineOptions where
  getPragmaOptions = optPragmaOptions
  setPragmaOptions opts st = st { optPragmaOptions = opts }
  lensPragmaOptions f st = f (optPragmaOptions st) <&> \ opts -> st { optPragmaOptions = opts }

instance LensPragmaOptions TCState where
  getPragmaOptions = (^.stPragmaOptions)
  setPragmaOptions = set stPragmaOptions
  lensPragmaOptions = stPragmaOptions

modifyPragmaOptions :: (PragmaOptions -> PragmaOptions) -> TCM ()
modifyPragmaOptions = modifyTC . mapPragmaOptions

---------------------------------------------------------------------------
-- ** Verbosity in the local pragma options
---------------------------------------------------------------------------

class LensVerbosity a where
  getVerbosity :: a -> Verbosity
  setVerbosity :: Verbosity -> a -> a
  mapVerbosity :: (Verbosity -> Verbosity) -> a -> a

  -- default implementations
  setVerbosity     = mapVerbosity . const
  mapVerbosity f a = setVerbosity (f $ getVerbosity a) a

instance LensVerbosity PragmaOptions where
  getVerbosity = optVerbose
  setVerbosity is opts = opts { optVerbose = is }

instance LensVerbosity TCState where
  getVerbosity = getVerbosity . getPragmaOptions
  mapVerbosity = mapPragmaOptions . mapVerbosity

modifyVerbosity :: (Verbosity -> Verbosity) -> TCM ()
modifyVerbosity = modifyTC . mapVerbosity

putVerbosity :: Verbosity -> TCM ()
putVerbosity = modifyTC . setVerbosity

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
  getCommandLineOptions = getCommandLineOptions . stPersistentState
  mapCommandLineOptions = updatePersistentState . mapCommandLineOptions

modifyCommandLineOptions :: (CommandLineOptions -> CommandLineOptions) -> TCM ()
modifyCommandLineOptions = modifyTC . mapCommandLineOptions

---------------------------------------------------------------------------
-- ** Safe mode
---------------------------------------------------------------------------

type SafeMode = Bool

class LensSafeMode a where
  getSafeMode :: a -> SafeMode
  setSafeMode :: SafeMode -> a -> a
  mapSafeMode :: (SafeMode -> SafeMode) -> a -> a

  -- default implementations
  setSafeMode     = mapSafeMode . const
  mapSafeMode f a = setSafeMode (f $ getSafeMode a) a

instance LensSafeMode PragmaOptions where
  getSafeMode = optSafe
  setSafeMode is opts = opts { optSafe = is } -- setSafeOption

instance LensSafeMode CommandLineOptions where
  getSafeMode = getSafeMode . getPragmaOptions
  mapSafeMode = mapPragmaOptions . mapSafeMode

instance LensSafeMode PersistentTCState where
  getSafeMode = getSafeMode . getCommandLineOptions
  mapSafeMode = mapCommandLineOptions . mapSafeMode

instance LensSafeMode TCState where
  getSafeMode = getSafeMode . getCommandLineOptions
  mapSafeMode = mapCommandLineOptions . mapSafeMode

modifySafeMode :: (SafeMode -> SafeMode) -> TCM ()
modifySafeMode = modifyTC . mapSafeMode

putSafeMode :: SafeMode -> TCM ()
putSafeMode = modifyTC . setSafeMode

isBuiltinWithSafePostulates :: FilePath -> TCM Bool
isBuiltinWithSafePostulates file = do
  libdir <- liftIO defaultLibDir
  let unsafeBuiltins =
        [ libdir </> "prim" </> "Agda" </> "Builtin" </> "TrustMe.agda"
        , libdir </> "prim" </> "Agda" </> "Builtin" </> "Equality" </> "Rewrite.agda"
        ]
  return $ (prefixPath libdir file) && not (elem file unsafeBuiltins)

---------------------------------------------------------------------------
-- ** Include directories
---------------------------------------------------------------------------

class LensIncludePaths a where
  getIncludePaths :: a -> [FilePath]
  setIncludePaths :: [FilePath] -> a -> a
  mapIncludePaths :: ([FilePath] -> [FilePath]) -> a -> a

  getAbsoluteIncludePaths :: a -> [AbsolutePath]
  setAbsoluteIncludePaths :: [AbsolutePath] -> a -> a
  mapAbsoluteIncludePaths :: ([AbsolutePath] -> [AbsolutePath]) -> a -> a

  -- default implementations
  setIncludePaths     = mapIncludePaths . const
  mapIncludePaths f a = setIncludePaths (f $ getIncludePaths a) a
  setAbsoluteIncludePaths     = mapAbsoluteIncludePaths . const
  mapAbsoluteIncludePaths f a = setAbsoluteIncludePaths (f $ getAbsoluteIncludePaths a) a

instance LensIncludePaths CommandLineOptions where
  getIncludePaths = optIncludePaths
  setIncludePaths is opts = opts { optIncludePaths = is }
  getAbsoluteIncludePaths = optAbsoluteIncludePaths
  setAbsoluteIncludePaths is opts = opts { optAbsoluteIncludePaths = is }

instance LensIncludePaths PersistentTCState where
  getIncludePaths = getIncludePaths . getCommandLineOptions
  mapIncludePaths = mapCommandLineOptions . mapIncludePaths
  getAbsoluteIncludePaths = getAbsoluteIncludePaths . getCommandLineOptions
  mapAbsoluteIncludePaths = mapCommandLineOptions . mapAbsoluteIncludePaths

instance LensIncludePaths TCState where
  getIncludePaths = getIncludePaths . getCommandLineOptions
  mapIncludePaths = mapCommandLineOptions . mapIncludePaths
  getAbsoluteIncludePaths = getAbsoluteIncludePaths . getCommandLineOptions
  mapAbsoluteIncludePaths = mapCommandLineOptions . mapAbsoluteIncludePaths

modifyIncludePaths :: ([FilePath] -> [FilePath]) -> TCM ()
modifyIncludePaths = modifyTC . mapIncludePaths

putIncludePaths :: [FilePath] -> TCM ()
putIncludePaths = modifyTC . setIncludePaths

modifyAbsoluteIncludePaths :: ([AbsolutePath] -> [AbsolutePath]) -> TCM ()
modifyAbsoluteIncludePaths = modifyTC . mapAbsoluteIncludePaths

putAbsoluteIncludePaths :: [AbsolutePath] -> TCM ()
putAbsoluteIncludePaths = modifyTC . setAbsoluteIncludePaths

---------------------------------------------------------------------------
-- ** Include directories
---------------------------------------------------------------------------

type PersistentVerbosity = Verbosity
class LensPersistentVerbosity a where
  getPersistentVerbosity :: a -> PersistentVerbosity
  setPersistentVerbosity :: PersistentVerbosity -> a -> a
  mapPersistentVerbosity :: (PersistentVerbosity -> PersistentVerbosity) -> a -> a

  -- default implementations
  setPersistentVerbosity     = mapPersistentVerbosity . const
  mapPersistentVerbosity f a = setPersistentVerbosity (f $ getPersistentVerbosity a) a

instance LensPersistentVerbosity PragmaOptions where
  getPersistentVerbosity = getVerbosity
  setPersistentVerbosity = setVerbosity

instance LensPersistentVerbosity CommandLineOptions where
  getPersistentVerbosity = getPersistentVerbosity . getPragmaOptions
  mapPersistentVerbosity = mapPragmaOptions . mapPersistentVerbosity

instance LensPersistentVerbosity PersistentTCState where
  getPersistentVerbosity = getPersistentVerbosity . getCommandLineOptions
  mapPersistentVerbosity = mapCommandLineOptions . mapPersistentVerbosity

instance LensPersistentVerbosity TCState where
  getPersistentVerbosity = getPersistentVerbosity . getCommandLineOptions
  mapPersistentVerbosity = mapCommandLineOptions . mapPersistentVerbosity

modifyPersistentVerbosity :: (PersistentVerbosity -> PersistentVerbosity) -> TCM ()
modifyPersistentVerbosity = modifyTC . mapPersistentVerbosity

putPersistentVerbosity :: PersistentVerbosity -> TCM ()
putPersistentVerbosity = modifyTC . setPersistentVerbosity
