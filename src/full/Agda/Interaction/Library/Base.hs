-- | Basic data types for library management.

module Agda.Interaction.Library.Base where

import Agda.Utils.Lens

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
data AgdaLibFile = AgdaLibFile
  { _libName     :: LibName     -- ^ The symbolic name of the library.
  , _libFile     :: FilePath    -- ^ Path to this @.agda-lib@ file (not content of the file).
  , _libIncludes :: [FilePath]  -- ^ Roots where to look for the modules of the library.
  , _libDepends  :: [LibName]   -- ^ Dependencies.
  }
  deriving (Show)

emptyLibFile :: AgdaLibFile
emptyLibFile = AgdaLibFile
  { _libName     = ""
  , _libFile     = ""
  , _libIncludes = []
  , _libDepends  = []
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
