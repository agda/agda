{-# LANGUAGE Strict #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE NondecreasingIndentation #-}

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
import Data.Foldable (traverse_)
import Data.Array.IO
import Data.Word
import qualified Data.ByteString as B
import qualified Data.Map as Map
import qualified Data.List as List
import Data.Function (on)

import qualified Codec.Compression.Zstd as Z

import GHC.Compact as C

import qualified Agda.TypeChecking.Monad.Benchmark as Bench

import Agda.TypeChecking.Serialise.Base
import Agda.TypeChecking.Serialise.Instances () --instance only

import Agda.TypeChecking.Monad

import Agda.Utils.Hash
import qualified Agda.Utils.HashTable as H
import Agda.Utils.IORef
import Agda.Utils.Null
import Agda.Utils.Serialize
import qualified Agda.Interaction.Options.ProfileOptions as Profile
import qualified Agda.Utils.MinimalArray.Lifted as AL
import qualified Agda.Utils.MinimalArray.MutableLifted as ML

import Agda.Utils.Impossible

-- Note that the Binary instance for Int writes 64 bits, but throws
-- away the 32 high bits when reading (at the time of writing, on
-- 32-bit machines). Word64 does not have these problems.

currentInterfaceVersion :: Word64
currentInterfaceVersion = 20250804 * 10 + 0

-- -- | The result of 'encode' and 'encodeInterface'.

-- data Encoded = Encoded
--   { uncompressed :: L.ByteString
--     -- ^ The uncompressed bytestring, without hashes and the interface
--     -- version.
--   , compressed :: L.ByteString
--     -- ^ The compressed bytestring.
--   }

type Encoded =
  ( Word32
  , AL.Array Node
  , AL.Array String
  , AL.Array TL.Text
  , AL.Array T.Text
  , AL.Array Integer
  , AL.Array VarSet
  , AL.Array Double)

-- | Encodes something as a tuple of hash-consed arrays. To ensure relocatability, file paths in
-- positions are replaced with module names.
encode :: EmbPrj a => a -> TCM Encoded
encode a = do
    collectStats <- hasProfileOption Profile.Serialize
    newD     <- liftIO $ emptyDict collectStats
    root     <- liftIO $ (`runReaderT` newD) $ icode a

    (nodeA, stringA, lTextA, sTextA, integerA, varSetA, doubleA) <-
      Bench.billTo [Bench.Serialization, Bench.Sort] $ liftIO $ do
        (,,,,,,) <$!> toArray (nodeD newD)
                 <*!> toArray (stringD newD)
                 <*!> toArray (lTextD newD)
                 <*!> toArray (sTextD newD)
                 <*!> toArray (integerD newD)
                 <*!> toArray (varSetD newD)
                 <*!> toArray (doubleD newD)

    -- Record reuse statistics.
    whenProfile Profile.Sharing $ do
      statistics "pointers" (termC newD)
    whenProfile Profile.Serialize $ do
      statistics "Integer"     (integerC newD)
      statistics "VarSet"      (varSetC newD)
      statistics "Lazy Text"   (lTextC newD)
      statistics "Strict Text" (sTextC newD)
      statistics "String"      (stringC newD)
      statistics "Double"      (doubleC newD)
      statistics "Node"        (nodeC newD)
      statistics "Shared Term" (termC newD)
      statistics "A.QName"     (qnameC newD)
      statistics "A.Name"      (nameC newD)
    when collectStats $ do
      stats <- map (second fromIntegral) <$> do
        liftIO $ List.sort <$> H.toList (stats newD)
      traverse_ (uncurry tickN) stats

   pure (root, nodeA, stringA, lTextA, sTextA, integerA, varSetA, doubleA)

    -- -- Encode hashmaps and root, and compress.
    -- !bits1 <- Bench.billTo [ Bench.Serialization, Bench.BinaryEncode ] $
    --   return $!! B.encode (root, nodeL, stringL, lTextL, sTextL, integerL, varSetL, doubleL)

    -- !cbits <- Bench.billTo [ Bench.Serialization, Bench.Compress ] $
    --   return $! L.fromStrict $! Z.compress 1 (L.toStrict bits1)

    -- let !x = B.encode currentInterfaceVersion <> cbits
    -- return (Encoded { uncompressed = bits1, compressed = x })

  where
    toArray :: HashMap k Word32 -> IO (AL.Array k)
    toArray tbl = do
      size <- H.size tbl
      arr <- ML.new size undefined
      H.forAssocs tbl \k v -> MV.unsafeWrite arr (fromIntegral v) k
      ML.unsafeFreeze arr

    statistics :: String -> FreshAndReuse -> TCM ()
    statistics kind far = do
      fresh <- liftIO $ getFresh far
#ifdef DEBUG_SERIALISATION
      reuse <- liftIO $ getReuse far
#endif
      tickN (kind ++ "  (fresh)") $ fromIntegral fresh
#ifdef DEBUG_SERIALISATION
      tickN (kind ++ " (reused)") $ fromIntegral reused
#endif


-- | Decodes an uncompressed bytestring (without extra hashes or magic
-- numbers). The result depends on the include path.
--
-- May throw IO exception.
decode :: EmbPrj a => ByteString -> TCM a
decode s = do
  mf   <- useTC stModuleToSource
  incs <- getIncludeDirs

  (mf, x) <- liftIO $ do
    (r, nodeA, stringA, lTextA, sTextA, integerA, varSetA, doubleA) <- deserialize s
    memo  <- ML.new (AL.size nodeA) MEEmpty
    mfRef <- newIORef mf

    let dec = Decode
          { nodeE    = nodeA
          , stringE  = stringA
          , lTextE   = lTextA
          , sTextE   = sTextA
          , integerE = integerA
          , varSetE  = varSetA
          , doubleE  = doubleA
          , nodeMemo = memo
          , modFile  = mfRef
          , includes = incs
          }

    r  <- runReaderT (value r) dec
    mf <- readIORef mfRef
    pure (mf, r)

  setTCLens stModuleToSource mf
  -- "Compact" the interfaces (without breaking sharing) to
  -- reduce the amount of memory that is traversed by the
  -- garbage collector.
  Bench.billTo [Bench.Deserialization, Bench.Compaction] $
    liftIO (Just . C.getCompact <$> C.compactWithSharing x)


-- | Encode an interface as a bytestring
encodeInterface :: Interface -> TCM ByteString
encodeInterface i = do
  r <- encode i
  liftIO $ serialize (iSourceHash i, iFullHash i, currentInterfaceVersion, r)

-- | Encodes an interface. To ensure relocatability file paths in
-- positions are replaced with module names.
--
-- An uncompressed bytestring corresponding to the encoded interface
-- is returned.
encodeFile :: FilePath -> Interface -> TCM ByteString
encodeFile f i = do
  r <- encodeInterface i
  liftIO $ createDirectoryIfMissing True (takeDirectory f)
  liftIO $ B.writeFile f (compressed r)
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
       then error "Wrong interface version."
       else case Z.decompress (L.toStrict s') of
         Z.Skip         -> error "decompression error"
         Z.Error e      -> error e
         Z.Decompress s -> pure s

  case s of
    Right s  -> decode $ L.fromStrict s
    Left err -> do
      reportSLn "import.iface" 5 $
        "Error when decoding interface file: " ++ err
      return Nothing

-- decodeHashes :: ByteString -> Maybe (Hash, Hash)
-- decodeHashes s
--   | L.length s < 16 = Nothing
--   | otherwise       = Just $ B.runGet getH $ L.take 16 s
--   where getH = (,) <$> B.get <*> B.get

decodeFile :: FilePath -> TCM (Maybe Interface)
decodeFile f = decodeInterface =<< liftIO (L.readFile f)
