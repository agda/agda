-- | Basic data types for library management.

module Agda.Interaction.Library.Base where

import Prelude hiding (null)

import Control.DeepSeq
import qualified Control.Exception as E

import Control.Monad.Except
import Control.Monad.State
import Control.Monad.Writer        ( WriterT, runWriterT, MonadWriter, tell )
import Control.Monad.IO.Class      ( MonadIO(..) )

import Data.Bifunctor              ( first , second )
import Data.Char                   ( isDigit )
import Data.Function               ( (&), on )
import Data.Hashable               ( Hashable )
import qualified Data.List         as List
import Data.Map                    ( Map )
import qualified Data.Map          as Map
import Data.Semigroup              ( Semigroup(..) )
import Data.Text                   ( Text, unpack )
import qualified Data.Text         as T

import GHC.Generics                ( Generic )

import System.Directory

import Agda.Interaction.Options.Warnings

import Agda.Syntax.Common.Pretty
import Agda.Syntax.Position

import Agda.Utils.IO               ( showIOException )
import Agda.Utils.Lens
import Agda.Utils.List             ( chopWhen )
import Agda.Utils.List1            ( List1, toList )
import Agda.Utils.List2            ( List2, toList )
import qualified Agda.Utils.List1  as List1
import Agda.Utils.Null

-- | A symbolic library name.
--
--   Library names are structured into the base name and a suffix of version
--   numbers, e.g. @mylib-1.2.3@.  The version suffix is optional.
data LibName = LibName
  { libNameBase    :: Text
      -- ^ Actual library name.
  , libNameVersion :: [Integer]
      -- ^ Major version, minor version, subminor version, etc., all non-negative.
  } deriving (Eq, Show, Generic)

-- | In comparisons, a missing version number is assumed to be infinity.
--   E.g. @foo > foo-2.2 > foo-2.0.1 > foo-2 > foo-1.0@.
instance Ord LibName where
  compare = compare `on` versionMeasure
    where
      versionMeasure :: LibName -> (Text, Bool, [Integer])
      versionMeasure (LibName rx vs) = (rx, null vs, vs)

instance Pretty LibName where
  pretty = \case
    LibName base [] -> pretty base
    LibName base vs -> hcat [ pretty base, "-", text $ List.intercalate "." $ map show vs ]

-- | Split a library name into basename and a list of version numbers.
--
--   > parseLibName "foo-1.2.3"    == LibName "foo" [1, 2, 3]
--   > parseLibName "foo-01.002.3" == LibName "foo" [1, 2, 3]
--
--   Note that because of leading zeros, @parseLibName@ is not injective.
--   (@prettyShow . parseLibName@ would produce a normal form.)
parseLibName :: String -> LibName
parseLibName s =
  case span (\ c -> isDigit c || c == '.') (reverse s) of
    (v, '-' : x) | valid vs ->
      LibName (T.pack $ reverse x) $ reverse $ map (read . reverse) vs
      where
        vs = chopWhen (== '.') v
        valid [] = False
        valid vs = not $ any null vs
    _ -> LibName (T.pack s) []

data LibrariesFile = LibrariesFile
  { lfPath   :: FilePath
      -- ^ E.g. @~/.agda/libraries@.
  , lfExists :: Bool
       -- ^ The libraries file might not exist,
       --   but we may print its assumed location in error messages.
  } deriving (Show, Generic)

-- | A symbolic executable name.
--
type ExeName = Text
type ExeMap  = Map ExeName FilePath

data ExecutablesFile = ExecutablesFile
  { efPath   :: FilePath
      -- ^ E.g. @~/.agda/executables@.
  , efExists :: Bool
       -- ^ The executables file might not exist,
       --   but we may print its assumed location in error messages.
  } deriving (Show, Generic)

-- | The special name @\".\"@ is used to indicated that the current directory
--   should count as a project root.
--
libNameForCurrentDir :: LibName
libNameForCurrentDir = LibName "." []

-- | A file can either belong to a project located at a given root
--   containing an .agda-lib file, or be part of the default project.
data ProjectConfig
  = ProjectConfig
    { configRoot         :: FilePath
        -- ^ Directory which contains the @.agda-lib@ file for the current project.
    , configAgdaLibFile  :: FilePath
        -- ^ @.agda-lib@ file relative to 'configRoot' (filename only, no directory).
    , configAbove        :: !Int
        -- ^ How many directories above the Agda file is the @.agda-lib@ file located?
    }
  | DefaultProjectConfig
  deriving Generic

-- | The options from an @OPTIONS@ pragma (or a @.agda-lib@ file).
--
-- In the future it might be nice to switch to a more structured
-- representation. Note that, currently, there is not a one-to-one
-- correspondence between list elements and options.
data OptionsPragma = OptionsPragma
  { pragmaStrings :: [String]
    -- ^ The options.
  , pragmaRange :: Range
    -- ^ The range of the options in the pragma (not including things
    -- like an @OPTIONS@ keyword).
  }
  deriving Show

instance Semigroup OptionsPragma where
  OptionsPragma { pragmaStrings = ss1, pragmaRange = r1 } <>
    OptionsPragma { pragmaStrings = ss2, pragmaRange = r2 } =
    OptionsPragma
      { pragmaStrings = ss1 ++ ss2
      , pragmaRange   = fuseRanges r1 r2
      }

instance Monoid OptionsPragma where
  mempty  = OptionsPragma { pragmaStrings = [], pragmaRange = noRange }
  mappend = (<>)

-- | Ranges are not forced.

instance NFData OptionsPragma where
  rnf (OptionsPragma a _) = rnf a

-- | Content of a @.agda-lib@ file.
--
data AgdaLibFile = AgdaLibFile
  { _libName     :: LibName     -- ^ The symbolic name of the library.
  , _libFile     :: FilePath    -- ^ Path to this @.agda-lib@ file (not content of the file).
  , _libAbove    :: !Int        -- ^ How many directories above the
                                --   Agda file is the @.agda-lib@ file
                                --   located?
  , _libIncludes :: [FilePath]  -- ^ Roots where to look for the modules of the library.
  , _libDepends  :: [LibName]   -- ^ Dependencies.
  , _libPragmas  :: OptionsPragma
                                -- ^ Default pragma options for all files in the library.
  }
  deriving (Show, Generic)

emptyLibFile :: AgdaLibFile
emptyLibFile = AgdaLibFile
  { _libName     = empty
  , _libFile     = ""
  , _libAbove    = 0
  , _libIncludes = []
  , _libDepends  = []
  , _libPragmas  = mempty
  }

---------------------------------------------------------------------------
-- * Lenses
---------------------------------------------------------------------------

-- ** Lenses for 'ProjectConfig'

lensConfigAbove :: Lens' ProjectConfig Int
lensConfigAbove f = \case
  DefaultProjectConfig -> DefaultProjectConfig <$ f 0
  c@ProjectConfig{} -> f (configAbove c) <&> \ !i -> c{ configAbove = i }

-- ** Lenses for 'AgdaLibFile'

libName :: Lens' AgdaLibFile LibName
libName f a = f (_libName a) <&> \ x -> a { _libName = x }

libFile :: Lens' AgdaLibFile FilePath
libFile f a = f (_libFile a) <&> \ x -> a { _libFile = x }

libAbove :: Lens' AgdaLibFile Int
libAbove f a = f (_libAbove a) <&> \ x -> a { _libAbove = x }

libIncludes :: Lens' AgdaLibFile [FilePath]
libIncludes f a = f (_libIncludes a) <&> \ x -> a { _libIncludes = x }

libDepends :: Lens' AgdaLibFile [LibName]
libDepends f a = f (_libDepends a) <&> \ x -> a { _libDepends = x }

libPragmas :: Lens' AgdaLibFile OptionsPragma
libPragmas f a = f (_libPragmas a) <&> \ x -> a { _libPragmas = x }


------------------------------------------------------------------------
-- * Library warnings and errors
------------------------------------------------------------------------

-- ** Position information

type LineNumber = Int

-- | Information about which @.agda-lib@ file we are reading
--   and from where in the @libraries@ file it came from.

data LibPositionInfo = LibPositionInfo
  { libFilePos :: Maybe FilePath -- ^ Name of @libraries@ file.
  , lineNumPos :: LineNumber     -- ^ Line number in @libraries@ file.
  , filePos    :: FilePath       -- ^ Library file.
  }
  deriving (Show, Generic)

-- ** Warnings

data LibWarning = LibWarning (Maybe LibPositionInfo) LibWarning'
  deriving (Show, Generic)

-- | Library Warnings.
data LibWarning'
  = UnknownField String
  deriving (Show, Generic)

libraryWarningName :: LibWarning -> WarningName
libraryWarningName (LibWarning c (UnknownField{})) = LibUnknownField_

-- * Errors

data LibError = LibError (Maybe LibPositionInfo) LibError'
  deriving (Show, Generic)

-- | Collected errors while processing library files.
--
data LibError'
  = LibrariesFileNotFound FilePath
      -- ^ The user specified replacement for the default @libraries@ file does not exist.
  | LibNotFound LibrariesFile LibName
      -- ^ Raised when a library name could not successfully be resolved
      --   to an @.agda-lib@ file.
      --
  | AmbiguousLib LibName (List2 AgdaLibFile)
      -- ^ Raised when a library name is defined in several @.agda-lib files@.
  | SeveralAgdaLibFiles FilePath (List2 FilePath)
      -- ^ The given project root contains more than one @.agda-lib@ file.
  | LibParseError LibParseError
      -- ^ The @.agda-lib@ file could not be parsed.
  | ReadError
      -- ^ An I/O Error occurred when reading a file.
      E.IOException
        -- ^ The caught exception
      String
        -- ^ Explanation when this error occurred.
  | DuplicateExecutable
      -- ^ The @executables@ file contains duplicate entries.
      FilePath
        -- ^ Name of the @executables@ file.
      Text
        -- ^ Name of the executable that is defined twice.
      (List2 (LineNumber, FilePath))
        -- ^ The resolutions of the executable.
  deriving (Show, Generic)

-- | Exceptions thrown by the @.agda-lib@ parser.
--
data LibParseError
  = BadLibraryName String
      -- ^ An invalid library name, e.g., containing spaces.
  | ReadFailure FilePath E.IOException
      -- ^ I/O error while reading file.
  | MissingFields (List1 String)
      -- ^ Missing these mandatory fields.
  | DuplicateFields (List1 String)
      -- ^ These fields occur each more than once.
  | MissingFieldName LineNumber
      -- ^ At the given line number, a field name is missing before the @:@.
  | BadFieldName LineNumber String
      -- ^ At the given line number, an invalid field name is encountered before the @:@.
      --   (E.g., containing spaces.)
  | MissingColonForField LineNumber String
      -- ^ At the given line number, the given field is not followed by @:@.
  | ContentWithoutField LineNumber
      -- ^ At the given line number, indented text (content) is not preceded by a field.
  deriving (Show, Generic)

-- ** Raising warnings and errors

-- | Collection of 'LibError's and 'LibWarning's.
--
type LibErrWarns = [Either LibError LibWarning]

warnings :: MonadWriter LibErrWarns m => List1 LibWarning -> m ()
warnings = tell . map Right . toList

warnings' :: MonadWriter LibErrWarns m => List1 LibWarning' -> m ()
warnings' = tell . map (Right . LibWarning Nothing) . toList

raiseErrors' :: MonadWriter LibErrWarns m => List1 LibError' -> m ()
raiseErrors' = tell . map (Left . (LibError Nothing)) . toList

raiseErrors :: MonadWriter LibErrWarns m => List1 LibError -> m ()
raiseErrors = tell . map Left . toList


------------------------------------------------------------------------
-- * Library Monad
------------------------------------------------------------------------

-- | Collects 'LibError's and 'LibWarning's.
--
type LibErrorIO = WriterT LibErrWarns (StateT LibState IO)

-- | Throws 'LibErrors' exceptions, still collects 'LibWarning's.
type LibM = ExceptT LibErrors (WriterT [LibWarning] (StateT LibState IO))

type LibState = LibCache

-- | Cache locations of project configurations and parsed @.agda-lib@ files.
data LibCache = LibCache
  { projectConfigs :: !(Map FilePath ProjectConfig)
      -- ^ Map from directories to paths of closest enclosing @.agda-lib@
      --   files (or 'DefaultProjectConfig' if there are none).
  , agdaLibFiles   :: !(Map FilePath AgdaLibFile)
      -- ^ Contents of @.agda-lib@ files that have already been parsed.
  }
  deriving (Generic)

-- | Collected errors when processing an @.agda-lib@ file.
--
data LibErrors = LibErrors
  { libErrorsInstalledLibraries :: [AgdaLibFile]
  , libErrors                   :: List1 LibError
  } deriving (Show, Generic)

runLibM :: LibM a -> LibState -> IO ((Either LibErrors a, [LibWarning]), LibState)
runLibM m s = m & runExceptT & runWriterT & (`runStateT` s)

getCachedProjectConfig
  :: (MonadState LibState m, MonadIO m)
  => FilePath -> m (Maybe ProjectConfig)
getCachedProjectConfig path = do
  path <- liftIO $ canonicalizePath path
  Map.lookup path <$> gets projectConfigs

storeCachedProjectConfig
  :: (MonadState LibState m, MonadIO m)
  => FilePath -> ProjectConfig -> m ()
storeCachedProjectConfig path conf = do
  path <- liftIO $ canonicalizePath path
  modify \ s -> s { projectConfigs = Map.insert path conf $ projectConfigs s }

getCachedAgdaLibFile
  :: (MonadState LibState m, MonadIO m)
  => FilePath -> m (Maybe AgdaLibFile)
getCachedAgdaLibFile path = do
  path <- liftIO $ canonicalizePath path
  Map.lookup path <$> gets agdaLibFiles

storeCachedAgdaLibFile
  :: (MonadState LibState m, MonadIO m)
  => FilePath -> AgdaLibFile -> m ()
storeCachedAgdaLibFile path lib = do
  path <- liftIO $ canonicalizePath path
  modify \ s -> s { agdaLibFiles = Map.insert path lib $ agdaLibFiles s }

------------------------------------------------------------------------
-- * Prettyprinting errors and warnings
------------------------------------------------------------------------

-- | Pretty-print 'LibError'.
formatLibError :: [AgdaLibFile] -> LibError -> Doc
formatLibError installed (LibError mc e) =
  case (mc, e) of
    (Just c, LibParseError err) -> sep  [ formatLibPositionInfo c err, pretty e ]
    (_     , LibNotFound{}    ) -> vcat [ pretty e, prettyInstalledLibraries installed ]
    _ -> pretty e


-- | Pretty-print 'LibErrors'.
formatLibErrors :: LibErrors -> Doc
formatLibErrors (LibErrors libs errs) =
  vcat $  map (formatLibError libs) $ List1.toList errs

-- | Does a parse error contain a line number?
hasLineNumber :: LibParseError -> Maybe LineNumber
hasLineNumber = \case
  BadLibraryName       _   -> Nothing
  ReadFailure          _ _ -> Nothing
  MissingFields        _   -> Nothing
  DuplicateFields      _   -> Nothing
  MissingFieldName     l   -> Just l
  BadFieldName         l _ -> Just l
  MissingColonForField l _ -> Just l
  ContentWithoutField  l   -> Just l

-- UNUSED:
-- -- | Does a parse error contain the name of the parsed file?
-- hasFilePath :: LibParseError -> Maybe FilePath
-- hasFilePath = \case
--   BadLibraryName       _   -> Nothing
--   ReadFailure          f _ -> Just f
--   MissingFields        _   -> Nothing
--   DuplicateFields      _   -> Nothing
--   MissingFieldName     _   -> Nothing
--   BadFieldName         _ _ -> Nothing
--   MissingColonForField _ _ -> Nothing
--   ContentWithoutField  _   -> Nothing

-- | Compute a position position prefix.
--
--   Depending on the error to be printed, it will
--
--   - either give the name of the @libraries@ file and a line inside it,
--
--   - or give the name of the @.agda-lib@ file.
--
formatLibPositionInfo :: LibPositionInfo -> LibParseError -> Doc
formatLibPositionInfo (LibPositionInfo libFile lineNum file) = \case

  -- If we couldn't even read the @.agda-lib@ file, report error in the @libraries@ file.
  ReadFailure _ _
    | Just lf <- libFile
      -> hcat [ text lf, ":", pretty lineNum, ":" ]
    | otherwise
      -> empty

  -- If the parse error comes with a line number, print it here.
  e | Just l <- hasLineNumber e
      -> hcat [ text file, ":", pretty l, ":" ]
    | otherwise
      -> hcat [ text file, ":" ]

prettyInstalledLibraries :: [AgdaLibFile] -> Doc
prettyInstalledLibraries installed =
  vcat $ ("Installed libraries:" :) $
    map (nest 2) $
    if null installed then ["(none)"]
    else [ sep [ pretty $ _libName l, nest 2 $ parens $ text $ _libFile l ]
         | l <- installed
         ]

-- | Pretty-print library management error without position info.

instance Pretty LibError' where
  pretty = \case

    LibrariesFileNotFound path -> sep
      [ text "Libraries file not found:"
      , text path
      ]

    LibNotFound file lib -> vcat $
      [ hcat [ "Library '", pretty lib, "' not found." ]
      , sep [ "Add the path to its .agda-lib file to"
            , nest 2 $ text $ "'" ++ lfPath file ++ "'"
            , "to install."
            ]
      ]

    AmbiguousLib lib tgts -> vcat $
      sep [ hcat [ "Ambiguous library '", pretty lib, "'." ]
            , "Could refer to any one of"
          ]
        : [ nest 2 $ pretty (_libName l) <+> parens (text $ _libFile l) | l <- toList tgts ]

    SeveralAgdaLibFiles root files -> vcat $
      sep [ "The project root", pretty root ]
        : "may contain only one .agda-lib file, but I found several:"
        : map (("-" <+>) . pretty) (List.sort $ toList files)

    LibParseError err -> pretty err

    ReadError e msg -> vcat
      [ text $ msg
      , text $ showIOException e
      ]

    DuplicateExecutable exeFile exe paths -> vcat $
      hcat [ "Duplicate entries for executable '", (text . unpack) exe, "' in ", text exeFile, ":" ] :
      map (\ (ln, fp) -> nest 2 $ (pretty ln <> colon) <+> text fp) (toList paths)

-- | Print library file parse error without position info.
--
instance Pretty LibParseError where
  pretty = \case

    BadLibraryName s -> sep
      [ "Bad library name:", quotes (text s) ]
    ReadFailure file e -> vcat
      [ hsep [ "Failed to read library file", text file <> "." ]
      , "Reason:" <+> text (showIOException e)
      ]

    MissingFields   xs -> "Missing"   <+> listFields xs
    DuplicateFields xs -> "Duplicate" <+> listFields xs

    MissingFieldName     l   -> atLine l $ "Missing field name"
    BadFieldName         l s -> atLine l $ "Bad field name" <+> text (show s)
    MissingColonForField l s -> atLine l $ "Missing ':' for field " <+> text (show s)
    ContentWithoutField  l   -> atLine l $ "Missing field"

    where
    listFields xs = hsep $ fieldS xs : list xs
    fieldS xs     = singPlural xs "field:" "fields:"
    list          = punctuate comma . map (quotes . text) . toList
    atLine l      = id
    -- The line number will be printed by 'formatLibPositionInfo'!
    -- atLine l doc  = hsep [ text (show l) <> ":", doc ]


instance Pretty LibWarning where
  pretty (LibWarning mc w) =
    case mc of
      Nothing -> pretty w
      Just (LibPositionInfo _ _ file) -> hcat [ text file, ":"] <+> pretty w

instance Pretty LibWarning' where
  pretty (UnknownField s) = text $ "Unknown field '" ++ s ++ "'"

------------------------------------------------------------------------
-- Hashable instances
------------------------------------------------------------------------

instance Hashable LibName

------------------------------------------------------------------------
-- Null instances
------------------------------------------------------------------------

instance Null LibName where
  empty = LibName empty empty
  null (LibName a b) = null a && null b

instance Null LibCache where
  empty = LibCache empty empty
  null (LibCache a b) = null a && null b

------------------------------------------------------------------------
-- NFData instances
------------------------------------------------------------------------

instance NFData ExecutablesFile
instance NFData LibrariesFile
instance NFData ProjectConfig
instance NFData AgdaLibFile
instance NFData LibName
instance NFData LibCache
instance NFData LibPositionInfo
instance NFData LibWarning
instance NFData LibWarning'
instance NFData LibError
instance NFData LibError'
instance NFData LibErrors
instance NFData LibParseError
instance NFData E.IOException where rnf _ = ()
