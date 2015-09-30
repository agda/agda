-- Andreas, Makoto, Francesco 2014-10-15 AIM XX:
-- -O2 does not have any noticable effect on runtime
-- but sabotages cabal repl with -Werror
-- (due to a conflict with --interactive warning)
-- {-# OPTIONS_GHC -O2                      #-}

-- | Structure-sharing serialisation of Agda interface files.

-- -!-!-!-!-!-!-!-!-!-!-!-!-!-!-!-!-!-!-!-!-!-!-!-!-!-!-!-!-!-!-!-!-!-!-
-- NOTE: Every time the interface format is changed the interface
-- version number should be bumped _in the same patch_.
-- -!-!-!-!-!-!-!-!-!-!-!-!-!-!-!-!-!-!-!-!-!-!-!-!-!-!-!-!-!-!-!-!-!-!-

module Agda.TypeChecking.Serialise
  ( encode, encodeFile, encodeInterface
  , decode, decodeFile, decodeInterface, decodeHashes
  , EmbPrj
  )
  where

import Control.Applicative
import Control.Arrow (second)
import Control.DeepSeq
import qualified Control.Exception as E
import Control.Monad
import Control.Monad.Reader
import Control.Monad.State.Strict

import Data.Array.IArray
import Data.Word
import qualified Data.ByteString.Lazy as L
import qualified Data.HashTable.IO as H
import qualified Data.Map as Map
import qualified Data.Binary as B
import qualified Data.Binary.Get as B
import qualified Data.Binary.Put as B
import qualified Data.List as List
import Data.Function

import qualified Codec.Compression.GZip as G

import qualified Agda.TypeChecking.Monad.Benchmark as Bench

import Agda.TypeChecking.Serialise.Base
import Agda.TypeChecking.Serialise.Instances ()

import Agda.TypeChecking.Monad

import Agda.Utils.Hash
import Agda.Utils.IORef
import Agda.Utils.Lens

import Agda.Utils.Except

-- Note that the Binary instance for Int writes 64 bits, but throws
-- away the 32 high bits when reading (at the time of writing, on
-- 32-bit machines). Word64 does not have these problems.

currentInterfaceVersion :: Word64
currentInterfaceVersion = 20150930 * 10 + 0

-- | Encodes something. To ensure relocatability file paths in
-- positions are replaced with module names.

encode :: EmbPrj a => a -> TCM L.ByteString
encode a = do
    collectStats <- hasVerbosity "profile.serialize" 20
    fileMod <- sourceToModule
    newD@(Dict nD sD bD iD dD _tD
      _nameD
      _qnameD
      nC sC bC iC dC tC
      nameC
      qnameC
      stats _ _) <- liftIO $ emptyDict collectStats
    root <- liftIO $ (`runReaderT` newD) $ do
       icodeFileMod fileMod
       icode a
    nL <- benchSort $ l nD
    sL <- benchSort $ l sD
    bL <- benchSort $ l bD
    iL <- benchSort $ l iD
    dL <- benchSort $ l dD
    -- Record reuse statistics.
    verboseS "profile.sharing" 10 $ do
      statistics "pointers" tC
    verboseS "profile.serialize" 10 $ do
      statistics "Integer"  iC
      statistics "String"   sC
      statistics "ByteString" bC
      statistics "Double"   dC
      statistics "Node"     nC
      statistics "Shared Term" tC
      statistics "A.QName"  qnameC
      statistics "A.Name"  nameC
    when collectStats $ do
      stats <- Map.fromList . map (second toInteger) <$> do
        liftIO $ H.toList stats
      modifyStatistics $ Map.union stats
    -- Encode hashmaps and root, and compress.
    bits1 <- Bench.billTo [ Bench.Serialization, Bench.BinaryEncode ] $
      return $!! B.encode (root, nL, sL, bL, iL, dL)
    let compressParams = G.defaultCompressParams
          { G.compressLevel    = G.bestSpeed
          , G.compressStrategy = G.huffmanOnlyStrategy
          }
    cbits <- Bench.billTo [ Bench.Serialization, Bench.Compress ] $
      return $!! G.compressWith compressParams bits1
    let x = B.encode currentInterfaceVersion `L.append` cbits
    return x
  where
    l h = List.map fst . List.sortBy (compare `on` snd) <$> H.toList h
    benchSort = Bench.billTo [Bench.Serialization, Bench.Sort] . liftIO
    statistics :: String -> IORef FreshAndReuse -> TCM ()
    statistics kind ioref = do
      FreshAndReuse fresh reused <- liftIO $ readIORef ioref
      tickN (kind ++ "  (fresh)") $ fromIntegral fresh
      tickN (kind ++ " (reused)") $ fromIntegral reused


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

-- | Decodes something. The result depends on the include path.
--
-- Returns 'Nothing' if the input does not start with the right magic
-- number or some other decoding error is encountered.

decode :: EmbPrj a => L.ByteString -> TCM (Maybe a)
decode s = do
  mf   <- use stModuleToSource
  incs <- getIncludeDirs

  -- Note that B.runGetState and G.decompress can raise errors if the
  -- input is malformed. The decoder is (intended to be) strict enough
  -- to ensure that all such errors can be caught by the handler here.

  shared <- sharedFun

  (mf, r) <- liftIO $ E.handle (\(E.ErrorCall s) -> noResult s) $ do

    (ver, s, _) <- return $ runGetState B.get s 0
    if ver /= currentInterfaceVersion
     then noResult "Wrong interface version."
     else do

      ((r, nL, sL, bL, iL, dL), s, _) <-
        return $ runGetState B.get (G.decompress s) 0
      if s /= L.empty
         -- G.decompress seems to throw away garbage at the end, so
         -- the then branch is possibly dead code.
       then noResult "Garbage at end."
       else do

        st <- St (ar nL) (ar sL) (ar bL) (ar iL) (ar dL)
                <$> liftIO H.new
                <*> return mf <*> return incs
                <*> return shared
        (r, st) <- runStateT (runExceptT (value r)) st
        return (Just (modFile st), r)

  case mf of
    Nothing -> return ()
    Just mf -> stModuleToSource .= mf

  case r of
    Right x   -> return (Just x)
    Left  err -> do
      reportSLn "import.iface" 5 $ "Error when decoding interface file"
      -- Andreas, 2014-06-11 deactivated debug printing
      -- in order to get rid of dependency of Serialize on TCM.Pretty
      -- reportSDoc "import.iface" 5 $
      --   text "Error when decoding interface file:"
      --   $+$ nest 2 (prettyTCM err)
      return Nothing

  where
  ar l = listArray (0, List.genericLength l - 1) l

  noResult s = return (Nothing, Left $ GenericError s)

encodeInterface :: Interface -> TCM L.ByteString
encodeInterface i = L.append hashes <$> encode i
  where
    hashes :: L.ByteString
    hashes = B.runPut $ B.put (iSourceHash i) >> B.put (iFullHash i)

-- | Encodes something. To ensure relocatability file paths in
-- positions are replaced with module names.

encodeFile :: FilePath -> Interface -> TCM ()
encodeFile f i = liftIO . L.writeFile f =<< encodeInterface i

-- | Decodes something. The result depends on the include path.
--
-- Returns 'Nothing' if the file does not start with the right magic
-- number or some other decoding error is encountered.

decodeInterface :: L.ByteString -> TCM (Maybe Interface)
decodeInterface s = decode $ L.drop 16 s

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
    i <- icod_ topLevelModuleName
    liftIO $ H.insert hmap absolutePath i
