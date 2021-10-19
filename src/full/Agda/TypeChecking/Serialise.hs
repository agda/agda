{-# LANGUAGE CPP #-}

-- Andreas, Makoto, Francesco 2014-10-15 AIM XX:
-- -O2 does not have any noticable effect on runtime
-- but sabotages cabal repl with -Werror
-- (due to a conflict with --interactive warning)
-- {-# OPTIONS_GHC -O2                      #-}

-- | Structure-sharing serialisation of Agda interface files.

-- -!-!-!-!-!-!-!-!-!-!-!-!-!-!-!-!-!-!-!-!-!-!-!-!-!-!-!-!-!-!-!-!-!-!-
-- NOTE: Every time the interface format is changed the interface
-- version number should be bumped _in the same patch_.
--
-- See 'currentInterfaceVersion' below.
--
-- -!-!-!-!-!-!-!-!-!-!-!-!-!-!-!-!-!-!-!-!-!-!-!-!-!-!-!-!-!-!-!-!-!-!-

module Agda.TypeChecking.Serialise
  ( encode, encodeFile, encodeInterface
  , decode, decodeFile, decodeInterface, decodeHashes
  , EmbPrj
  )
  where

import System.Directory ( createDirectoryIfMissing )
import System.FilePath ( takeDirectory )

import Control.Arrow (second)
import Control.DeepSeq
import qualified Control.Exception as E
import Control.Monad
import Control.Monad.Except
import Control.Monad.Reader
import Control.Monad.State.Strict

import Data.Array.IArray
import Data.Word
import qualified Data.ByteString.Builder as L
import qualified Data.ByteString.Lazy as L
import qualified Data.HashTable.IO as H
import qualified Data.Map as Map
import qualified Data.Binary as B
import qualified Data.Binary.Get as B
import qualified Data.Binary.Put as B
import qualified Data.List as List
import Data.Function
#if !(MIN_VERSION_base(4,11,0))
import Data.Semigroup((<>))
#endif

import qualified Codec.Compression.GZip as G
import qualified Codec.Compression.Zlib.Internal as Z

#if __GLASGOW_HASKELL__ >= 804
import GHC.Compact as C
#endif

import qualified Agda.TypeChecking.Monad.Benchmark as Bench

import Agda.TypeChecking.Serialise.Base
import Agda.TypeChecking.Serialise.Instances () --instance only

import Agda.TypeChecking.Monad

import Agda.Utils.FileName (canonicalizeAbsolutePath)
import Agda.Utils.Hash
import Agda.Utils.IORef

-- Note that the Binary instance for Int writes 64 bits, but throws
-- away the 32 high bits when reading (at the time of writing, on
-- 32-bit machines). Word64 does not have these problems.

currentInterfaceVersion :: Word64
currentInterfaceVersion = 20211019 * 10 + 0

-- | The result of 'encode' and 'encodeInterface'.

data Encoded = Encoded
  { uncompressed :: L.ByteString
    -- ^ The uncompressed bytestring, without hashes and the interface
    -- version.
  , compressed :: L.ByteString
    -- ^ The compressed bytestring.
  }

-- | Encodes something. To ensure relocatability file paths in
-- positions are replaced with module names.

encode :: EmbPrj a => a -> TCM Encoded
encode a = do
    collectStats <- hasVerbosity "profile.serialize" 20
    fileMod <- sourceToModule
    newD@(Dict nD ltD stD bD iD dD _tD
      _nameD
      _qnameD
      nC ltC stC bC iC dC tC
      nameC
      qnameC
      stats _ _) <- liftIO $ emptyDict collectStats
    root <- liftIO $ (`runReaderT` newD) $ do
       icodeFileMod fileMod  -- Only fills absPathD from fileMod
       icode a
    nL  <- benchSort $ l nD
    stL <- benchSort $ l stD
    ltL <- benchSort $ l ltD
    bL  <- benchSort $ l bD
    iL  <- benchSort $ l iD
    dL  <- benchSort $ l dD
    -- Record reuse statistics.
    verboseS "profile.sharing" 10 $ do
      statistics "pointers" tC
    verboseS "profile.serialize" 10 $ do
      statistics "Integer"     iC
      statistics "Lazy Text"   ltC
      statistics "Strict Text" stC
      statistics "Text"        bC
      statistics "Double"      dC
      statistics "Node"        nC
      statistics "Shared Term" tC
      statistics "A.QName"     qnameC
      statistics "A.Name"      nameC
    when collectStats $ do
      stats <- Map.fromList . map (second toInteger) <$> do
        liftIO $ H.toList stats
      modifyStatistics $ Map.union stats
    -- Encode hashmaps and root, and compress.
    bits1 <- Bench.billTo [ Bench.Serialization, Bench.BinaryEncode ] $
      return $!! B.encode (root, nL, ltL, stL, bL, iL, dL)
    let compressParams = G.defaultCompressParams
          { G.compressLevel    = G.bestSpeed
          , G.compressStrategy = G.huffmanOnlyStrategy
          }
    cbits <- Bench.billTo [ Bench.Serialization, Bench.Compress ] $
      return $!! G.compressWith compressParams bits1
    let x = B.encode currentInterfaceVersion `L.append` cbits
    return (Encoded { uncompressed = bits1, compressed = x })
  where
    l h = List.map fst . List.sortBy (compare `on` snd) <$> H.toList h
    benchSort = Bench.billTo [Bench.Serialization, Bench.Sort] . liftIO
    statistics :: String -> IORef FreshAndReuse -> TCM ()
    statistics kind ioref = do
      FreshAndReuse fresh
#ifdef DEBUG
                          reused
#endif
                                 <- liftIO $ readIORef ioref
      tickN (kind ++ "  (fresh)") $ fromIntegral fresh
#ifdef DEBUG
      tickN (kind ++ " (reused)") $ fromIntegral reused
#endif

-- encode :: EmbPrj a => a -> TCM L.ByteString
-- encode a = do
--     fileMod <- sourceToModule
--     (x, shared, total) <- liftIO $ do
--       newD@(Dict nD sD iD dD _ _ _ _ _ stats _) <- emptyDict fileMod
--       root <- runReaderT (icode a) newD
--       nL <- l nD; sL <- l sD; iL <- l iD; dL <- l dD
--       (shared, total) <- readIORef stats
--       return (B.encode currentInterfaceVersion `L.append`
--               G.compress (B.encode (root, nL, sL, iL, dL)), shared, total)
--     verboseS "profile.sharing" 10 $ do
--       tickN "pointers (reused)" $ fromIntegral shared
--       tickN "pointers" $ fromIntegral total
--     return x
--   where
--   l h = List.map fst . List.sortBy (compare `on` snd) <$> H.toList h

-- | Decodes an uncompressed bytestring (without extra hashes or magic
-- numbers). The result depends on the include path.
--
-- Returns 'Nothing' if a decoding error is encountered.

decode :: EmbPrj a => L.ByteString -> TCM (Maybe a)
decode s = do
  mf   <- useTC stModuleToSource
  incs <- getIncludeDirs

  -- Note that runGetState can raise errors if the input is malformed.
  -- The decoder is (intended to be) strict enough to ensure that all
  -- such errors can be caught by the handler here.

  (mf, r) <- liftIO $ E.handle (\(E.ErrorCall s) -> noResult s) $ do

    ((r, nL, ltL, stL, bL, iL, dL), s, _) <- return $ runGetState B.get s 0
    if s /= L.empty
     then noResult "Garbage at end."
     else do

      st <- St (ar nL) (ar ltL) (ar stL) (ar bL) (ar iL) (ar dL)
              <$> liftIO H.new
              <*> return mf <*> return incs
      (r, st) <- runStateT (runExceptT (value r)) st
      return (Just $ modFile st, r)

  forM_ mf (setTCLens stModuleToSource)

  case r of
    Right x -> do
#if __GLASGOW_HASKELL__ >= 804
      -- "Compact" the interfaces (without breaking sharing) to
      -- reduce the amount of memory that is traversed by the
      -- garbage collector.
      Bench.billTo [Bench.Deserialization, Bench.Compaction] $
        liftIO (Just . C.getCompact <$> C.compactWithSharing x)
#else
      return (Just x)
#endif
    Left err -> do
      reportSLn "import.iface" 5 $ "Error when decoding interface file"
      -- Andreas, 2014-06-11 deactivated debug printing
      -- in order to get rid of dependency of Serialize on TCM.Pretty
      -- reportSDoc "import.iface" 5 $
      --   "Error when decoding interface file:"
      --   $+$ nest 2 (prettyTCM err)
      return Nothing

  where
  ar l = listArray (0, List.genericLength l - 1) l

  noResult s = return (Nothing, Left $ GenericError s)

encodeInterface :: Interface -> TCM Encoded
encodeInterface i = do
  r <- encode i
  return (r { compressed = L.append hashes (compressed r) })
  where
    hashes :: L.ByteString
    hashes = B.runPut $ B.put (iSourceHash i) >> B.put (iFullHash i)

-- | Encodes an interface. To ensure relocatability file paths in
-- positions are replaced with module names.
--
-- An uncompressed bytestring corresponding to the encoded interface
-- is returned.

encodeFile :: FilePath -> Interface -> TCM L.ByteString
encodeFile f i = do
  r <- encodeInterface i
  liftIO $ createDirectoryIfMissing True (takeDirectory f)
  liftIO $ L.writeFile f (compressed r)
  return (uncompressed r)

-- | Decodes an interface. The result depends on the include path.
--
-- Returns 'Nothing' if the file does not start with the right magic
-- number or some other decoding error is encountered.

decodeInterface :: L.ByteString -> TCM (Maybe Interface)
decodeInterface s = do

  -- Note that runGetState and the decompression code below can raise
  -- errors if the input is malformed. The decoder is (intended to be)
  -- strict enough to ensure that all such errors can be caught by the
  -- handler here or the one in decode.

  s <- liftIO $
       E.handle (\(E.ErrorCall s) -> return (Left s)) $
       E.evaluate $
       let (ver, s', _) = runGetState B.get (L.drop 16 s) 0 in
       if ver /= currentInterfaceVersion
       then Left "Wrong interface version."
       else Right $
            L.toLazyByteString $
            Z.foldDecompressStreamWithInput
              (\s -> (L.byteString s <>))
              (\s -> if L.null s
                     then mempty
                     else error "Garbage at end.")
              (\err -> error (show err))
              (Z.decompressST Z.gzipFormat Z.defaultDecompressParams)
              s'

  case s of
    Right s  -> decode s
    Left err -> do
      reportSLn "import.iface" 5 $
        "Error when decoding interface file: " ++ err
      return Nothing

decodeHashes :: L.ByteString -> Maybe (Hash, Hash)
decodeHashes s
  | L.length s < 16 = Nothing
  | otherwise       = Just $ B.runGet getH $ L.take 16 s
  where getH = (,) <$> B.get <*> B.get

decodeFile :: FilePath -> TCM (Maybe Interface)
decodeFile f = decodeInterface =<< liftIO (L.readFile f)

-- | Store a 'SourceToModule' (map from 'AbsolutePath' to 'TopLevelModuleName')
--   as map from 'AbsolutePath' to 'Int32', in order to directly get the identifiers
--   from absolute pathes rather than going through top level module names.
icodeFileMod
  :: SourceToModule
     -- ^ Maps file names to the corresponding module names.
     --   Must contain a mapping for every file name that is later encountered.
  -> S ()
icodeFileMod fileMod = do
  hmap <- asks absPathD
  forM_ (Map.toList fileMod) $ \ (absolutePath, topLevelModuleName) -> do
    -- Andreas, 2020-08-11, issue #4828.
    -- Expand symlinks before storing in the dictonary.
    absolutePath <- liftIO $ canonicalizeAbsolutePath absolutePath
    i <- icod_ topLevelModuleName
    liftIO $ H.insert hmap absolutePath i
