{-# LANGUAGE Strict #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE NondecreasingIndentation #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE UnboxedTuples #-}
{-# OPTIONS_GHC -Wno-redundant-bang-patterns #-}
{-# OPTIONS_GHC -Wunused-imports #-}

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
  ( InterfacePrefix
  , Encoded
  , encode
  , encodeFile
  , decode
  , decodeFile
  , decodeInterface
  , deserializeInterface
  , deserializeHashes
  )
  where

import Prelude hiding ( null )

import System.Directory ( createDirectoryIfMissing )
import System.FilePath ( takeDirectory )

import qualified Control.Exception as E
import Control.Monad
import Control.Monad.Reader
import Control.Monad.Trans.Maybe

import Data.Foldable (traverse_)
import Data.Word
import Data.ByteString (ByteString)
import qualified Data.ByteString as B
import qualified Data.ByteString.Lazy as LB
import qualified Data.List as List
import qualified Data.Text as T
import qualified Data.Text.Lazy as TL

import qualified Codec.Compression.Zstd as Z

import Agda.Interaction.Options.ProfileOptions qualified as Profile
import Agda.TypeChecking.Monad
import Agda.TypeChecking.Monad.Benchmark qualified as Bench
import Agda.TypeChecking.Serialise.Base
import Agda.TypeChecking.Serialise.Instances () -- instances only

import Agda.Utils.CompactRegion qualified as Compact
import Agda.Utils.Hash
import Agda.Utils.HashTable qualified as H
import Agda.Utils.IORef
import Agda.Utils.MinimalArray.Lifted qualified as AL
import Agda.Utils.MinimalArray.MutableLifted qualified as ML
import Agda.Utils.Monad ((<*!>))
import Agda.Utils.Serialize
import Agda.Utils.Tuple (second)
import Agda.Utils.VarSet (VarSet)

import Agda.Utils.Impossible

#include "MachDeps.h"

currentInterfaceVersion :: Word64
currentInterfaceVersion = 20260214 * 10 + 0

ifaceVersionSize :: Int
ifaceVersionSize = SIZEOF_WORD64

ifacePrefixSize :: Int
ifacePrefixSize = 2 * hashSize + ifaceVersionSize

type InterfacePrefix =
  ( Hash     -- sourceHash
  , Hash     -- fullHash
  , Word64   -- interface version
  )

-- | Hash-consed encoding of a value.
type Encoded =
  ( Word32             -- index of root Node
  , AL.Array Node
  , AL.Array String
  , AL.Array TL.Text
  , AL.Array T.Text
  , AL.Array Integer
  , AL.Array VarSet
  , AL.Array Double
  )

-- | Encodes something as a hash-consed tuple of arrays. To ensure relocatability, file paths in
--   positions are replaced with module names.
encode :: EmbPrj a => a -> TCM Encoded
encode a = do
  collectStats <- hasProfileOption Profile.Serialize
  newD         <- liftIO $ emptyDict collectStats
  root         <- liftIO $ (`runReaderT` newD) $ icode a

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
  where
    toArray :: H.HashTableLU k Word32 -> IO (AL.Array k)
    toArray tbl = do
      size <- H.size tbl
      arr <- ML.new size undefined
      H.forAssocs tbl \k v -> ML.write arr (fromIntegral v) k
      ML.unsafeFreeze arr

    statistics :: String -> FreshAndReuse -> TCM ()
    statistics kind far = do
      fresh <- liftIO $ getFresh far
#ifdef DEBUG_SERIALISATION
      reused <- liftIO $ getReuse far
#endif
      tickN (kind ++ "  (fresh)") $ fromIntegral fresh
#ifdef DEBUG_SERIALISATION
      tickN (kind ++ " (reused)") $ fromIntegral reused
#endif

-- | Decode a hash-consed value. The result depends on the include path.
decode :: EmbPrj a => Encoded -> MaybeT TCM a
decode enc = stateSessionLensM lensModuleToSource \mf -> do
  includes <- lift $ getIncludeDirs
  arena    <- liftIO $ Compact.new (2 ^ 12) -- 4 KB blocks

  let compactElems :: AL.Array a -> IO (AL.Array a)
      compactElems = AL.traverseIO' (Compact.add arena)

  tryDecode $ do
    let (r, nodeA, stringA, lTextA, sTextA, integerA, varSetA, doubleA) = enc

    stringA      <- compactElems stringA
    lTextA       <- compactElems lTextA
    sTextA       <- compactElems sTextA
    integerA     <- compactElems integerA
    varSetA      <- compactElems varSetA
    doubleA      <- compactElems doubleA
    filePathMemo <- H.empty
    nodeMemo     <- ML.new (AL.size nodeA) MEEmpty
    modFile      <- newIORef mf
    let dec = Decode nodeMemo arena nodeA stringA lTextA sTextA integerA varSetA
                     doubleA filePathMemo modFile includes
    res <- runReaderT (value r) dec
    mf  <- readIORef modFile
    pure (res, mf)
  -- -- "Compact" the interfaces (without breaking sharing) to
  -- -- reduce the amount of memory that is traversed by the
  -- -- garbage collector.
  -- lift $ Bench.billTo [Bench.Deserialization, Bench.Compaction] $
  --   liftIO $ C.getCompact <$!> C.compactWithSharing res

getInterfacePrefix :: Interface -> InterfacePrefix
getInterfacePrefix i =
  (iSourceHash i, iFullHash i, currentInterfaceVersion)

-- | Serialize an interface prefix + an encoded interface to a lazy bytestring.
--   The result is lazy in order to avoid copying data when we prepend the
--   prefix to the compressed interface bytestring.
serializeEncodedInterface :: InterfacePrefix -> Encoded -> TCM LB.ByteString
serializeEncodedInterface prefix i = do
  let doCompress i = pure $! Z.compress 1 i -- we outline this to prevent let-lifting by GHC
      {-# NOINLINE doCompress #-}           -- which could ruin the benchmark timing.
  (prefix, i) <- Bench.billTo [Bench.Serialization, Bench.BinaryEncode] $ liftIO $
                   (,) <$!> serialize prefix <*!> serialize i
  i <- Bench.billTo [Bench.Serialization, Bench.Compress] $ doCompress i
  pure $! LB.fromStrict prefix <> LB.fromStrict i

-- | Convert ErrorCall-s (which are assumed to be deserialization errors) to
--   MaybeT TCM.
tryDecode :: IO a -> MaybeT TCM a
tryDecode act = MaybeT do
  res <- liftIO ((Right <$!> act) `E.catch` \(E.ErrorCall err) -> pure (Left err))
  case res of
    Left err -> do
      reportSLn "import.iface" 5 $ "Error when decoding interface file: " ++ err
      pure Nothing
    Right a -> pure $ Just a

-- | Decode an interface from a bytestring. We check the stored interface
--   version against the current interface version, but we don't do anything
--   with the hash prefix.
decodeInterface :: ByteString -> MaybeT TCM Interface
decodeInterface bstr = decode =<< deserializeInterface bstr

deserializeInterface :: ByteString -> MaybeT TCM Encoded
deserializeInterface bstr = do
  let decompressionError =
        tryDecode $ E.throwIO $ E.ErrorCall "decompression error"
  let (prefix, i) = B.splitAt ifacePrefixSize bstr
  ((_, _, ver) :: InterfacePrefix) <- tryDecode $ deserialize prefix
  if ver /= currentInterfaceVersion then
    decompressionError
  else case Z.decompress i of
    Z.Skip         -> decompressionError
    Z.Error e      -> decompressionError
    Z.Decompress i -> tryDecode $ deserialize i

--------------------------------------------------------------------------------

-- | Encodes an interface. To ensure relocatability file paths in positions are
-- replaced with module names.
-- A hash-consed and compacted interface is returned.
encodeFile :: FilePath -> Interface -> TCM Interface
encodeFile f i = do
  let prefix = getInterfacePrefix i
  iEncoded <- encode i
  bstr <- serializeEncodedInterface prefix iEncoded
  i <- Bench.billTo [Bench.Deserialization] $
    maybe __IMPOSSIBLE__ pure =<< runMaybeT (decode @Interface iEncoded)

  -- reload interface from the bytestring instead
  -- i <- Bench.billTo [Bench.Deserialization] $
  --     maybe __IMPOSSIBLE__ pure =<<
  --       runMaybeT (decode =<< deserializeInterface (LB.toStrict bstr))

  liftIO $ createDirectoryIfMissing True (takeDirectory f)
  liftIO $ LB.writeFile f bstr
  pure i

decodeFile :: FilePath -> TCM (Maybe Interface)
decodeFile f = runMaybeT (decodeInterface =<< liftIO (B.readFile f))

deserializeHashes :: ByteString -> IO (Maybe (Hash, Hash))
deserializeHashes bstr =
  (Just <$!> deserialize bstr)
  `E.catch` \(E.ErrorCall _) -> pure Nothing
