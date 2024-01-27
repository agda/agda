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

import Prelude hiding ( null )

import System.Directory ( createDirectoryIfMissing )
import System.FilePath ( takeDirectory )

import Control.Arrow (second)
import Control.DeepSeq
import qualified Control.Exception as E
import Control.Monad
import Control.Monad.Except
import Control.Monad.IO.Class ( MonadIO(..) )
import Control.Monad.Reader
import Control.Monad.State.Strict
import Control.Monad.ST.Trans

import Data.Array.IArray
import Data.Array.IO
import Data.Word
import Data.Int (Int32)
import Data.ByteString.Lazy    ( ByteString )
import Data.ByteString.Builder ( byteString, toLazyByteString )
import qualified Data.ByteString.Lazy as L
import qualified Data.Map as Map
import qualified Data.Binary as B
import qualified Data.Binary.Get as B
import qualified Data.Binary.Put as B
import qualified Data.List as List
import Data.Function (on)

import qualified Codec.Compression.GZip as G
import qualified Codec.Compression.Zlib.Internal as Z

import GHC.Compact as C

import qualified Agda.TypeChecking.Monad.Benchmark as Bench

import Agda.TypeChecking.Serialise.Base
import Agda.TypeChecking.Serialise.Instances () --instance only

import Agda.TypeChecking.Monad

import Agda.Utils.Hash
import qualified Agda.Utils.HashTable as H
import Agda.Utils.IORef
import Agda.Utils.Null
import qualified Agda.Utils.ProfileOptions as Profile

import Agda.Utils.Impossible

-- Note that the Binary instance for Int writes 64 bits, but throws
-- away the 32 high bits when reading (at the time of writing, on
-- 32-bit machines). Word64 does not have these problems.

currentInterfaceVersion :: Word64
currentInterfaceVersion = 20240124 * 10 + 1

-- | The result of 'encode' and 'encodeInterface'.

data Encoded = Encoded
  { uncompressed :: ByteString
    -- ^ The uncompressed bytestring, without hashes and the interface
    -- version.
  , compressed :: ByteString
    -- ^ The compressed bytestring.
  }

-- | Encodes something. To ensure relocatability file paths in
-- positions are replaced with module names.

encode :: EmbPrj a => a -> TCM Encoded
encode a = do
    collectStats <- hasProfileOption Profile.Serialize
    newD@(Dict nD ltD stD bD iD dD _tD
      _nameD
      _qnameD
      nC ltC stC bC iC dC tC
      nameC
      qnameC
      stats _) <- liftIO $ emptyDict collectStats
    root <- liftIO $ (`runReaderT` newD) $ icode a
    nL  <- benchSort $ l nD
    stL <- benchSort $ l stD
    ltL <- benchSort $ l ltD
    bL  <- benchSort $ l bD
    iL  <- benchSort $ l iD
    dL  <- benchSort $ l dD
    -- Record reuse statistics.
    whenProfile Profile.Sharing $ do
      statistics "pointers" tC
    whenProfile Profile.Serialize $ do
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
      stats <- Map.fromListWith __IMPOSSIBLE__ . map (second toInteger) <$> do
        liftIO $ List.sort <$> H.toList stats
      modifyStatistics $ Map.unionWith (+) stats
    -- Encode hashmaps and root, and compress.
    bits1 <- Bench.billTo [ Bench.Serialization, Bench.BinaryEncode ] $
      return $!! B.encode (root, nL, ltL, stL, bL, iL, dL)
    let compressParams = G.defaultCompressParams
          { G.compressLevel    = G.bestSpeed
          , G.compressStrategy = G.huffmanOnlyStrategy
          }
    cbits <- Bench.billTo [ Bench.Serialization, Bench.Compress ] $
      return $!! G.compressWith compressParams bits1
    let x = B.encode currentInterfaceVersion <> cbits
    return (Encoded { uncompressed = bits1, compressed = x })
  where
    l h = List.map fst . List.sortBy (compare `on` snd) <$> H.toList h
    benchSort = Bench.billTo [Bench.Serialization, Bench.Sort] . liftIO
    statistics :: String -> IORef FreshAndReuse -> TCM ()
    statistics kind ioref = do
      FreshAndReuse fresh
#ifdef DEBUG_SERIALISATION
                          reused
#endif
                                 <- liftIO $ readIORef ioref
      tickN (kind ++ "  (fresh)") $ fromIntegral fresh
#ifdef DEBUG_SERIALISATION
      tickN (kind ++ " (reused)") $ fromIntegral reused
#endif

-- encode :: EmbPrj a => a -> TCM ByteString
-- encode a = do
--     fileMod <- sourceToModule
--     (x, shared, total) <- liftIO $ do
--       newD@(Dict nD sD iD dD _ _ _ _ _ stats _) <- emptyDict fileMod
--       root <- runReaderT (icode a) newD
--       nL <- l nD; sL <- l sD; iL <- l iD; dL <- l dD
--       (shared, total) <- readIORef stats
--       return (B.encode currentInterfaceVersion <>
--               G.compress (B.encode (root, nL, sL, iL, dL)), shared, total)
--     whenProfile Profile.Sharing $ do
--       tickN "pointers (reused)" $ fromIntegral shared
--       tickN "pointers" $ fromIntegral total
--     return x
--   where
--   l h = List.map fst . List.sortBy (compare `on` snd) <$> H.toList h

newtype ListLike a = ListLike { unListLike :: Array Int32 a }

instance B.Binary a => B.Binary (ListLike a) where
  put = __IMPOSSIBLE__ -- Will never serialise this
  get = fmap ListLike $ runSTArray $ do
    n <- lift (B.get :: B.Get Int)
    arr <- newArray_ (0, fromIntegral n - 1) :: STT s B.Get (STArray s Int32 a)

    -- We'd like to use 'for_ [0..n-1]' here, but unfortunately GHC doesn't unfold
    -- the list construction and so performs worse than the hand-written version.
    let
      getMany i = if i == n then return () else do
        x <- lift B.get
        unsafeWriteSTArray arr i x
        getMany (i + 1)
    () <- getMany 0

    return arr

-- | Decodes an uncompressed bytestring (without extra hashes or magic
-- numbers). The result depends on the include path.
--
-- Returns 'Nothing' if a decoding error is encountered.

decode :: EmbPrj a => ByteString -> TCM (Maybe a)
decode s = do
  mf   <- useTC stModuleToSource
  incs <- getIncludeDirs

  -- Note that runGetState can raise errors if the input is malformed.
  -- The decoder is (intended to be) strict enough to ensure that all
  -- such errors can be caught by the handler here.

  res <- liftIO $ E.handle (\(E.ErrorCall s) -> pure $ Left s) $ do
    ((r, nL, ltL, stL, bL, iL, dL), s, _) <- return $ runGetState B.get s 0
    let ar = unListLike
    when (not (null s)) $ E.throwIO $ E.ErrorCall "Garbage at end."
    let nL' = ar nL
    st <- St nL' (ar ltL) (ar stL) (ar bL) (ar iL) (ar dL)
            <$> liftIO (newArray (bounds nL') MEEmpty)
            <*> return mf <*> return incs
    (r, st) <- runStateT (value r) st
    let !mf = modFile st
    return $ Right (mf, r)

  case res of
    Left s -> do
      reportSLn "import.iface" 5 $ "Error when decoding interface file: " ++ s
      pure Nothing

    Right (mf, x) -> do
      setTCLens stModuleToSource mf
      -- "Compact" the interfaces (without breaking sharing) to
      -- reduce the amount of memory that is traversed by the
      -- garbage collector.
      Bench.billTo [Bench.Deserialization, Bench.Compaction] $
        liftIO (Just . C.getCompact <$> C.compactWithSharing x)


encodeInterface :: Interface -> TCM Encoded
encodeInterface i = do
  r <- encode i
  return r{ compressed = hashes <> compressed r }
  where
    hashes :: ByteString
    hashes = B.runPut $ B.put (iSourceHash i) >> B.put (iFullHash i)

-- | Encodes an interface. To ensure relocatability file paths in
-- positions are replaced with module names.
--
-- An uncompressed bytestring corresponding to the encoded interface
-- is returned.

encodeFile :: FilePath -> Interface -> TCM ByteString
encodeFile f i = do
  r <- encodeInterface i
  liftIO $ createDirectoryIfMissing True (takeDirectory f)
  liftIO $ L.writeFile f (compressed r)
  return (uncompressed r)

-- | Decodes an interface. The result depends on the include path.
--
-- Returns 'Nothing' if the file does not start with the right magic
-- number or some other decoding error is encountered.

decodeInterface :: ByteString -> TCM (Maybe Interface)
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
            toLazyByteString $
            Z.foldDecompressStreamWithInput
              (\s -> (byteString s <>))
              (\s -> if null s
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

decodeHashes :: ByteString -> Maybe (Hash, Hash)
decodeHashes s
  | L.length s < 16 = Nothing
  | otherwise       = Just $ B.runGet getH $ L.take 16 s
  where getH = (,) <$> B.get <*> B.get

decodeFile :: FilePath -> TCM (Maybe Interface)
decodeFile f = decodeInterface =<< liftIO (L.readFile f)
