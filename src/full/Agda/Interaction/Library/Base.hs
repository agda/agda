
module Agda.Interaction.Library.Base where

-- | A symbolic library name.
--
type LibName = String

-- | The special name @\".\"@ is used to indicated that the current directory
--   should count as a project root.
--
libNameForCurrentDir :: LibName
libNameForCurrentDir = "."

-- | Content of a @.agda-lib@ file.
--
data AgdaLibFile = AgdaLib
  { libName     :: LibName     -- ^ The symbolic name of the library.
  , libFile     :: FilePath    -- ^ Path to this @.agda-lib@ file (not content of the file).
  , libIncludes :: [FilePath]  -- ^ Roots where to look for the modules of the library.
  , libDepends  :: [LibName]   -- ^ Dependencies.
  }
  deriving (Show)

emptyLibFile :: AgdaLibFile
emptyLibFile = AgdaLib { libName = "", libFile = "", libIncludes = [], libDepends = [] }
