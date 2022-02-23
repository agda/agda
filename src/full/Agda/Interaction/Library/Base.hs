-- | Basic data types for library management.

module Agda.Interaction.Library.Base where

import Control.Arrow ( first , second )
import Control.DeepSeq
import Control.Monad.Except
import Control.Monad.State
import Control.Monad.Writer
import Control.Monad.IO.Class ( MonadIO(..) )

import Data.Char ( isDigit )
import Data.Data ( Data )
import qualified Data.List as List
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Text ( Text )

import GHC.Generics (Generic)

import System.Directory
import System.FilePath

import Agda.Interaction.Options.Warnings

import Agda.Utils.FileName
import Agda.Utils.Lens
import Agda.Utils.Pretty

-- | A symbolic library name.
--
type LibName = String

data LibrariesFile = LibrariesFile
  { lfPath   :: FilePath
      -- ^ E.g. @~/.agda/libraries@.
  , lfExists :: Bool
       -- ^ The libraries file might not exist,
       --   but we may print its assumed location in error messages.
  } deriving (Show)

-- | A symbolic executable name.
--
type ExeName = Text

data ExecutablesFile = ExecutablesFile
  { efPath   :: FilePath
      -- ^ E.g. @~/.agda/executables@.
  , efExists :: Bool
       -- ^ The executables file might not exist,
       --   but we may print its assumed location in error messages.
  } deriving (Show, Data, Generic)

-- | The special name @\".\"@ is used to indicated that the current directory
--   should count as a project root.
--
libNameForCurrentDir :: LibName
libNameForCurrentDir = "."

-- | A file can either belong to a project located at a given root
--   containing one or more .agda-lib files, or be part of the default
--   project.
data ProjectConfig
  = ProjectConfig
    { configRoot         :: FilePath
    , configAgdaLibFiles :: [FilePath]
    }
  | DefaultProjectConfig
  deriving Generic

-- | Content of a @.agda-lib@ file.
--
data AgdaLibFile = AgdaLibFile
  { _libName     :: LibName     -- ^ The symbolic name of the library.
  , _libFile     :: FilePath    -- ^ Path to this @.agda-lib@ file (not content of the file).
  , _libIncludes :: [FilePath]  -- ^ Roots where to look for the modules of the library.
  , _libDepends  :: [LibName]   -- ^ Dependencies.
  , _libPragmas  :: [String]    -- ^ Default pragma options for all files in the library.
  }
  deriving (Show, Generic)

emptyLibFile :: AgdaLibFile
emptyLibFile = AgdaLibFile
  { _libName     = ""
  , _libFile     = ""
  , _libIncludes = []
  , _libDepends  = []
  , _libPragmas  = []
  }

-- | Lenses for AgdaLibFile

libName :: Lens' LibName AgdaLibFile
libName f a = f (_libName a) <&> \ x -> a { _libName = x }

libFile :: Lens' FilePath AgdaLibFile
libFile f a = f (_libFile a) <&> \ x -> a { _libFile = x }

libIncludes :: Lens' [FilePath] AgdaLibFile
libIncludes f a = f (_libIncludes a) <&> \ x -> a { _libIncludes = x }

libDepends :: Lens' [LibName] AgdaLibFile
libDepends f a = f (_libDepends a) <&> \ x -> a { _libDepends = x }

libPragmas :: Lens' [String] AgdaLibFile
libPragmas f a = f (_libPragmas a) <&> \ x -> a { _libPragmas = x }


------------------------------------------------------------------------
-- * Library warnings and errors
------------------------------------------------------------------------

type LineNumber = Int

data LibPositionInfo = LibPositionInfo
  { libFilePos :: Maybe FilePath -- ^ Name of @libraries@ file
  , lineNumPos :: LineNumber     -- ^ Line number in @libraries@ file.
  , filePos    :: FilePath       -- ^ Library file
  }
  deriving (Show, Data, Generic)

data LibWarning = LibWarning (Maybe LibPositionInfo) LibWarning'
  deriving (Show, Data, Generic)

-- | Library Warnings.
data LibWarning'
  = UnknownField String
  deriving (Show, Data, Generic)

data LibError = LibError (Maybe LibPositionInfo) LibError'

libraryWarningName :: LibWarning -> WarningName
libraryWarningName (LibWarning c (UnknownField{})) = LibUnknownField_

-- | Collected errors while processing library files.
--
data LibError'
  = LibNotFound LibrariesFile LibName
      -- ^ Raised when a library name could not successfully be resolved
      --   to an @.agda-lib@ file.
      --
  | AmbiguousLib LibName [AgdaLibFile]
      -- ^ Raised when a library name is defined in several @.agda-lib files@.
  | OtherError String
      -- ^ Generic error.
  deriving (Show)

-- | Cache locations of project configurations and parsed .agda-lib files
type LibState =
  ( Map FilePath ProjectConfig
  , Map FilePath AgdaLibFile
  )

-- | Collects 'LibError's and 'LibWarning's.
--
type LibErrorIO = WriterT [Either LibError LibWarning] (StateT LibState IO)

-- | Throws 'Doc' exceptions, still collects 'LibWarning's.
type LibM = ExceptT Doc (WriterT [LibWarning] (StateT LibState IO))

warnings :: MonadWriter [Either LibError LibWarning] m => [LibWarning] -> m ()
warnings = tell . map Right

warnings' :: MonadWriter [Either LibError LibWarning] m => [LibWarning'] -> m ()
warnings' = tell . map (Right . LibWarning Nothing)

-- UNUSED Liang-Ting Chen 2019-07-16
--warning :: MonadWriter [Either LibError LibWarning] m => LibWarning -> m ()
--warning = warnings . pure

raiseErrors' :: MonadWriter [Either LibError LibWarning] m => [LibError'] -> m ()
raiseErrors' = tell . map (Left . (LibError Nothing))

raiseErrors :: MonadWriter [Either LibError LibWarning] m => [LibError] -> m ()
raiseErrors = tell . map Left

getCachedProjectConfig
  :: (MonadState LibState m, MonadIO m)
  => FilePath -> m (Maybe ProjectConfig)
getCachedProjectConfig path = do
  path <- liftIO $ canonicalizePath path
  cache <- gets fst
  return $ Map.lookup path cache

storeCachedProjectConfig
  :: (MonadState LibState m, MonadIO m)
  => FilePath -> ProjectConfig -> m ()
storeCachedProjectConfig path conf = do
  path <- liftIO $ canonicalizePath path
  modify $ first $ Map.insert path conf

getCachedAgdaLibFile
  :: (MonadState LibState m, MonadIO m)
  => FilePath -> m (Maybe AgdaLibFile)
getCachedAgdaLibFile path = do
  path <- liftIO $ canonicalizePath path
  gets $ Map.lookup path . snd

storeCachedAgdaLibFile
  :: (MonadState LibState m, MonadIO m)
  => FilePath -> AgdaLibFile -> m ()
storeCachedAgdaLibFile path lib = do
  path <- liftIO $ canonicalizePath path
  modify $ second $ Map.insert path lib

------------------------------------------------------------------------
-- * Prettyprinting errors and warnings
------------------------------------------------------------------------

formatLibPositionInfo :: LibPositionInfo -> String -> Doc
formatLibPositionInfo (LibPositionInfo libFile lineNum file) err = text $
  let loc | Just lf <- libFile = lf ++ ":" ++ show lineNum ++ ": "
          | otherwise = ""
  in if "Failed to read" `List.isPrefixOf` err
     then loc
     else file ++ ":" ++ (if all isDigit (take 1 err) then "" else " ")

-- | Pretty-print 'LibError'.
formatLibError :: [AgdaLibFile] -> LibError -> Doc
formatLibError installed (LibError mc e) = prefix <+> body where
  prefix = case mc of
    Nothing                      -> ""
    Just c | OtherError err <- e -> formatLibPositionInfo c err
    _                            -> ""

  body = case e of
    LibNotFound file lib -> vcat $
      [ text $ "Library '" ++ lib ++ "' not found."
      , sep [ "Add the path to its .agda-lib file to"
            , nest 2 $ text $ "'" ++ lfPath file ++ "'"
            , "to install."
            ]
      , "Installed libraries:"
      ] ++
      map (nest 2)
         (if null installed then ["(none)"]
          else [ sep [ text $ _libName l, nest 2 $ parens $ text $ _libFile l ]
               | l <- installed ])

    AmbiguousLib lib tgts -> vcat $
      sep [ text $ "Ambiguous library '" ++ lib ++ "'."
            , "Could refer to any one of"
          ]
        : [ nest 2 $ text (_libName l) <+> parens (text $ _libFile l) | l <- tgts ]


    OtherError err -> text err

instance Pretty LibWarning where
  pretty (LibWarning mc w) = prefix <+> pretty w
    where
      prefix = case mc of
        Nothing -> ""
        Just c  -> formatLibPositionInfo c ""


instance Pretty LibWarning' where
  pretty (UnknownField s) = text $ "Unknown field '" ++ s ++ "'"

------------------------------------------------------------------------
-- NFData instances
------------------------------------------------------------------------

instance NFData ExecutablesFile
instance NFData ProjectConfig
instance NFData AgdaLibFile
instance NFData LibPositionInfo
instance NFData LibWarning
instance NFData LibWarning'
