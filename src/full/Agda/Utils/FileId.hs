-- | Translating between file paths and ids.
--
-- This module allows you to build a dictionary from file paths to some unique identifier
-- and to look up both file paths and identifiers in that dictionary.

module Agda.Utils.FileId where

import           Prelude               hiding (null)

import           Control.DeepSeq       (NFData)
import           Control.Monad.Except  (ExceptT)
import           Control.Monad.Reader  (ReaderT)
import           Control.Monad.State   (StateT)
import           Control.Monad.Trans   (MonadTrans, lift)

import           Data.Bifunctor        (second)
import           Data.EnumMap          (EnumMap)
import qualified Data.EnumMap          as EnumMap
import           Data.Map              (Map)
import qualified Data.Map              as Map
import           Data.Maybe            (fromMaybe)
import           Data.Word             (Word32)

import           GHC.Generics          (Generic)

import           Agda.Utils.CallStack  (HasCallStack)
import           Agda.Utils.FileName   (AbsolutePath)
import           Agda.Utils.Null       (Null(..))

import Agda.Utils.Impossible (__IMPOSSIBLE__)

type File = AbsolutePath

-- | Unique identifier of a file.
newtype FileId = FileId { theFileId :: Word32 }
  deriving (Eq, Ord, Show, Generic, Enum, Num)

-- * Mapping between files and their unique identifiers.

type FileToId = Map File FileId
type IdToFile = EnumMap FileId File

data FileDict = FileDict
  { fileToId :: FileToId
  , idToFile :: IdToFile
  } deriving (Generic)

-- | Translate a file to an ID; mapping must exist.
class GetFileId a where
  getFileId :: HasCallStack => a -> File -> FileId

-- | Translate a ID to a file; mapping must exist.
class GetIdFile a where
  getIdFile :: a -> FileId -> File

-- * Constructing a mapping between files and their unique identifiers.

data FileDictBuilder = FileDictBuilder
  { nextFileId :: FileId
  , fileDict   :: FileDict
  } deriving (Generic)

-- | Register a new file identifier or retrieve an existing one.
registerFileId :: File -> FileDictBuilder -> (FileId, FileDictBuilder)
registerFileId f d = second (fromMaybe d) $ registerFileId'' f d

-- | Register a new file identifier ('True') or retrieve an existing one ('False').
registerFileId' :: File -> FileDictBuilder -> ((FileId, Bool), FileDictBuilder)
registerFileId' f d =
  case registerFileId'' f d of
    (i, Nothing) -> ((i, False), d)
    (i, Just d') -> ((i, True), d')

-- | Register a new file identifier or retrieve an existing one.
--
--   If 'Nothing' is returned, the file was already registered.
registerFileId'' :: File -> FileDictBuilder -> (FileId, Maybe FileDictBuilder)
registerFileId''  f d@(FileDictBuilder n (FileDict fileToId idToFile)) =
  case Map.lookup f fileToId of
    Just i  -> (i, Nothing)
    Nothing -> (n, Just $ FileDictBuilder (n + 1) (FileDict fileToId' idToFile'))
  where
    fileToId' = Map.insert f n fileToId
    idToFile' = EnumMap.insert n f idToFile

-- * Monadic interface

class Monad m => MonadFileId m where
  fileFromId :: FileId -> m File
  idFromFile :: File -> m FileId

  default fileFromId :: (MonadTrans t, MonadFileId n, m ~ t n) => FileId -> m File
  fileFromId = lift . fileFromId

  default idFromFile :: (MonadTrans t, MonadFileId n, m ~ t n) => File -> m FileId
  idFromFile = lift . idFromFile

instance MonadFileId m => MonadFileId (ExceptT e m)
instance MonadFileId m => MonadFileId (ReaderT r m)
instance MonadFileId m => MonadFileId (StateT s m)

-- Instances for GetFileId

instance GetFileId FileToId where
  getFileId :: FileToId -> File -> FileId
  getFileId m f = Map.findWithDefault __IMPOSSIBLE__ f m

instance GetFileId FileDict where
  getFileId = getFileId . fileToId

instance GetFileId FileDictBuilder where
  getFileId = getFileId . fileDict

-- Instances for GetIdFile

instance GetIdFile IdToFile where
  getIdFile :: IdToFile -> FileId -> File
  getIdFile m i = EnumMap.findWithDefault __IMPOSSIBLE__ i m

instance GetIdFile FileDict where
  getIdFile = getIdFile . idToFile

instance GetIdFile FileDictBuilder where
  getIdFile = getIdFile . fileDict

-- Instances for Null

instance Null FileDict where
  empty = FileDict empty empty
  null (FileDict to fro) = null to && null fro

instance Null FileDictBuilder where
  empty = FileDictBuilder 1 empty
  null (FileDictBuilder _ d) = null d

-- Instances for NFData

instance NFData FileId
instance NFData FileDict
instance NFData FileDictBuilder
