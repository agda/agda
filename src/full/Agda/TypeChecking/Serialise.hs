{-# LANGUAGE CPP                       #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FlexibleInstances         #-}
{-# LANGUAGE ScopedTypeVariables       #-}

#if __GLASGOW_HASKELL__ >= 710
{-# LANGUAGE FlexibleContexts #-}
#endif

#if __GLASGOW_HASKELL__ <= 708
{-# LANGUAGE OverlappingInstances #-}
#endif

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
import Control.Monad.State.Strict (StateT, runStateT, gets, modify)

import Data.Array.IArray
import Data.Word
import qualified Data.ByteString.Lazy as L
import Data.Hashable
import qualified Data.HashTable.IO as H
import Data.Int (Int32)
import Data.Maybe
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set
import qualified Data.Binary as B
import qualified Data.Binary.Get as B
import qualified Data.Binary.Put as B
import qualified Data.List as List
import Data.Function
import Data.Typeable ( cast, Typeable, typeOf, TypeRep )

import qualified Codec.Compression.GZip as G

import qualified Agda.Compiler.Epic.Interface as Epic
import qualified Agda.Compiler.UHC.Pragmas.Base as CR
import qualified Agda.Compiler.UHC.ModuleInfo as UHC
import qualified Agda.Compiler.UHC.AuxAST as UHCA
import qualified Agda.Compiler.UHC.Naming as UHCN
import qualified Agda.Compiler.UHC.Bridge as UHCB

import Agda.Syntax.Common as Common
import Agda.Syntax.Concrete.Name as C
import qualified Agda.Syntax.Concrete as C
import qualified Agda.Syntax.Abstract as A
import Agda.Syntax.Info
import Agda.Syntax.Internal as I
import Agda.Syntax.Scope.Base
import Agda.Syntax.Position as P
-- import Agda.Syntax.Position (Position, Range, noRange)
-- import qualified Agda.Syntax.Position as P
import Agda.Syntax.Fixity
import Agda.Syntax.Notation
import Agda.Syntax.Literal
import qualified Agda.Compiler.JS.Syntax as JS
import qualified Agda.Interaction.Highlighting.Range   as HR
import qualified Agda.Interaction.Highlighting.Precise as HP
import Agda.Interaction.FindFile

import qualified Agda.TypeChecking.Monad.Benchmark as Bench

import Agda.TypeChecking.Monad
import Agda.TypeChecking.CompiledClause
import Agda.TypeChecking.Positivity.Occurrence
-- import Agda.TypeChecking.Pretty

import Agda.Utils.BiMap (BiMap)
import qualified Agda.Utils.BiMap as BiMap
import Agda.Utils.HashMap (HashMap)
import Agda.Utils.Hash
import qualified Agda.Utils.HashMap as HMap
import Agda.Utils.FileName
import Agda.Utils.IORef
import Agda.Utils.Lens
import Agda.Utils.Monad
import Agda.Utils.Permutation

import Agda.Utils.Except ( ExceptT, MonadError(throwError), runExceptT )

#include "undefined.h"
import Agda.Utils.Impossible

-- Note that the Binary instance for Int writes 64 bits, but throws
-- away the 32 high bits when reading (at the time of writing, on
-- 32-bit machines). Word64 does not have these problems.

currentInterfaceVersion :: Word64
currentInterfaceVersion = 20150829 * 10 + 0

-- | Constructor tag (maybe omitted) and argument indices.

type Node = [Int32]

-- | The type of hashtables used in this module.
--
-- A very limited amount of testing indicates that 'H.CuckooHashTable'
-- is somewhat slower than 'H.BasicHashTable', and that
-- 'H.LinearHashTable' and the hashtables from "Data.Hashtable" are
-- much slower.

#if defined(mingw32_HOST_OS) && defined(x86_64_HOST_ARCH)
type HashTable k v = H.CuckooHashTable k v
#else
type HashTable k v = H.BasicHashTable k v
#endif

-- | Structure providing fresh identifiers for hash map
--   and counting hash map hits (i.e. when no fresh identifier required).
data FreshAndReuse = FreshAndReuse
  { farFresh :: !Int32 -- ^ Number of hash map misses.
  , farReuse :: !Int32 -- ^ Number of hash map hits.
  }

farEmpty :: FreshAndReuse
farEmpty = FreshAndReuse 0 0

lensFresh :: Lens' Int32 FreshAndReuse
lensFresh f r = f (farFresh r) <&> \ i -> r { farFresh = i }

lensReuse :: Lens' Int32 FreshAndReuse
lensReuse f r = f (farReuse r) <&> \ i -> r { farReuse = i }

-- | Two 'A.QName's are equal if their @QNameId@ is equal.
type QNameId = [NameId]

-- | Computing a qualified names composed ID.
qnameId :: A.QName -> QNameId
qnameId (A.QName (A.MName ns) n) = map A.nameId $ n:ns

-- | State of the the encoder.
data Dict = Dict
  -- Dictionaries which are serialized:
  { nodeD        :: !(HashTable Node    Int32)    -- ^ Written to interface file.
  , stringD      :: !(HashTable String  Int32)    -- ^ Written to interface file.
  , bstringD     :: !(HashTable L.ByteString Int32) -- ^ Written to interface file.
  , integerD     :: !(HashTable Integer Int32)    -- ^ Written to interface file.
  , doubleD      :: !(HashTable Double  Int32)    -- ^ Written to interface file.
  -- Dicitionaries which are not serialized, but provide
  -- short cuts to speed up serialization:
  , termD        :: !(HashTable (Ptr Term) Int32) -- ^ Not written to interface file.
  -- Andreas, Makoto, AIM XXI
  -- Memoizing A.Name does not buy us much if we already memoize A.QName.
  , nameD        :: !(HashTable NameId  Int32)    -- ^ Not written to interface file.
  , qnameD       :: !(HashTable QNameId Int32)    -- ^ Not written to interface file.
  -- Fresh UIDs and reuse statistics:
  , nodeC        :: !(IORef FreshAndReuse)  -- counters for fresh indexes
  , stringC      :: !(IORef FreshAndReuse)
  , bstringC     :: !(IORef FreshAndReuse)
  , integerC     :: !(IORef FreshAndReuse)
  , doubleC      :: !(IORef FreshAndReuse)
  , termC        :: !(IORef FreshAndReuse)
  , nameC        :: !(IORef FreshAndReuse)
  , qnameC       :: !(IORef FreshAndReuse)
  , stats        :: !(HashTable String Int)
  , collectStats :: Bool
    -- ^ If @True@ collect in @stats@ the quantities of
    --   calls to @icode@ for each @Typeable a@.
  , absPathD     :: !(HashTable AbsolutePath Int32) -- ^ Not written to interface file.
  }

-- | Creates an empty dictionary.
emptyDict
  :: Bool
     -- ^ Collect statistics for @icode@ calls?
  -> IO Dict
emptyDict collectStats = Dict
  <$> H.new
  <*> H.new
  <*> H.new
  <*> H.new
  <*> H.new
  <*> H.new
  <*> H.new
  <*> H.new
  <*> newIORef farEmpty
  <*> newIORef farEmpty
  <*> newIORef farEmpty
  <*> newIORef farEmpty
  <*> newIORef farEmpty
  <*> newIORef farEmpty
  <*> newIORef farEmpty
  <*> newIORef farEmpty
  <*> H.new
  <*> pure collectStats
  <*> H.new

-- | Universal type, wraps everything.
data U    = forall a . Typeable a => U !a

-- | Univeral memo structure, to introduce sharing during decoding
type Memo = HashTable (Int32, TypeRep) U    -- (node index, type rep)

-- | State of the decoder.
data St = St
  { nodeE     :: !(Array Int32 Node)     -- ^ Obtained from interface file.
  , stringE   :: !(Array Int32 String)   -- ^ Obtained from interface file.
  , bstringE  :: !(Array Int32 L.ByteString) -- ^ Obtained from interface file.
  , integerE  :: !(Array Int32 Integer)  -- ^ Obtained from interface file.
  , doubleE   :: !(Array Int32 Double)   -- ^ Obtained from interface file.
  , nodeMemo  :: !Memo
    -- ^ Created and modified by decoder.
    --   Used to introduce sharing while deserializing objects.
  , modFile   :: !ModuleToSource
    -- ^ Maps module names to file names. Constructed by the decoder.
  , includes  :: [AbsolutePath]
    -- ^ The include directories.
  , mkShared  :: Term -> Term
  }

-- | Monad used by the encoder.

type S a = ReaderT Dict IO a

-- | Monad used by the decoder.
--
-- 'TCM' is not used because the associated overheads would make
-- decoding slower.

type R a = ExceptT TypeError (StateT St IO) a

-- | Throws an error which is suitable when the data stream is
-- malformed.

malformed :: R a
malformed = throwError $ GenericError "Malformed input."

class Typeable a => EmbPrj a where
  icode :: a -> S Int32  -- ^ Serialization (wrapper).
  icod_ :: a -> S Int32  -- ^ Serialization (worker).
  value :: Int32 -> R a  -- ^ Deserialization.

  icode a = do
    tickICode a
    icod_ a

-- | Increase entry for @a@ in 'stats'.
tickICode :: forall a. Typeable a => a -> S ()
tickICode _ = whenM (asks collectStats) $ do
    let key = "icode " ++ show (typeOf (undefined :: a))
    hmap <- asks stats
    liftIO $ do
      n <- fromMaybe 0 <$> H.lookup hmap key
      H.insert hmap key $! n + 1

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

-- | Data.Binary.runGetState is deprecated in favour of runGetIncremental.
--   Reimplementing it in terms of the new function. The new Decoder type contains
--   strict byte strings so we need to be careful not to feed the entire lazy byte
--   string to the decoder at once.
runGetState :: B.Get a -> L.ByteString -> B.ByteOffset -> (a, L.ByteString, B.ByteOffset)
runGetState g s n = feed (B.runGetIncremental g) (L.toChunks s)
  where
    feed (B.Done s n' x) ss     = (x, L.fromChunks (s : ss), n + n')
    feed (B.Fail _ _ err) _     = error err
    feed (B.Partial f) (s : ss) = feed (f $ Just s) ss
    feed (B.Partial f) []       = feed (f Nothing) []

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

#if __GLASGOW_HASKELL__ >= 710
instance {-# OVERLAPPING #-} EmbPrj String where
#else
instance EmbPrj String where
#endif
  icod_   = icodeString
  value i = (! i) `fmap` gets stringE

instance EmbPrj L.ByteString where
  icod_   = icodeX bstringD bstringC
  value i = (! i) `fmap` gets bstringE

instance EmbPrj Integer where
  icod_   = icodeInteger
  value i = (! i) `fmap` gets integerE

instance EmbPrj Word64 where
  icod_ i = icode2' (int32 q) (int32 r)
    where (q, r) = quotRem i (2^32)
          int32 :: Word64 -> Int32
          int32 = fromIntegral
  value = vcase valu where valu [a, b] = return $ n * mod (fromIntegral a) n + mod (fromIntegral b) n
                           valu _      = malformed
                           n = 2^32

instance EmbPrj Int32 where
  icod_ i = return i
  value i = return i

instance EmbPrj Int where
  icod_ i = return (fromIntegral i)
  value i = return (fromIntegral i)

instance EmbPrj Char where
  icod_ c = return (fromIntegral $ fromEnum c)
  value i = return (toEnum $ fromInteger $ toInteger i)

instance EmbPrj Double where
  icod_   = icodeDouble
  value i = (! i) `fmap` gets doubleE

instance EmbPrj () where
  icod_ () = icode0'
  value = vcase valu where valu [] = valu0 ()
                           valu _  = malformed

instance (EmbPrj a, EmbPrj b) => EmbPrj (a, b) where
  icod_ (a, b) = icode2' a b
  value = vcase valu where valu [a, b] = valu2 (,) a b
                           valu _      = malformed

instance (EmbPrj a, EmbPrj b, EmbPrj c) => EmbPrj (a, b, c) where
  icod_ (a, b, c) = icode3' a b c
  value = vcase valu where valu [a, b, c] = valu3 (,,) a b c
                           valu _         = malformed

instance (EmbPrj a, EmbPrj b) => EmbPrj (Either a b) where
  icod_ (Left  x) = icode1 0 x
  icod_ (Right x) = icode1 1 x
  value = vcase valu where valu [0, x] = valu1 Left  x
                           valu [1, x] = valu1 Right x
                           valu _   = malformed

instance EmbPrj a => EmbPrj (Maybe a) where
  icod_ Nothing  = icode0'
  icod_ (Just x) = icode1' x
  value = vcase valu where valu []  = valu0 Nothing
                           valu [x] = valu1 Just x
                           valu _   = malformed

instance EmbPrj Bool where
  icod_ True  = icode0'
  icod_ False = icode0 0
  value = vcase valu where valu []  = valu0 True
                           valu [0] = valu0 False
                           valu _   = malformed

instance EmbPrj AbsolutePath where
  icod_ file = do
    d <-  asks absPathD
    liftIO $ fromMaybe __IMPOSSIBLE__ <$> H.lookup d file
  value m = do
    m :: TopLevelModuleName
            <- value m
    mf      <- gets modFile
    incs    <- gets includes
    (r, mf) <- liftIO $ findFile'' incs m mf
    modify $ \s -> s { modFile = mf }
    case r of
      Left err -> throwError $ findErrorToTypeError m err
      Right f  -> return f

instance EmbPrj Position where
  icod_ (P.Pn file pos line col) = icode4' file pos line col
  value = vcase valu
    where
    valu [f, p, l, c] = valu4 P.Pn f p l c
    valu _            = malformed

instance EmbPrj TopLevelModuleName where
  icod_ (TopLevelModuleName a) = icode1' a
  value = vcase valu where valu [a] = valu1 TopLevelModuleName a
                           valu _   = malformed

#if __GLASGOW_HASKELL__ >= 710
instance {-# OVERLAPPABLE #-} EmbPrj a => EmbPrj [a] where
#else
instance EmbPrj a => EmbPrj [a] where
#endif
  icod_ xs = icodeN =<< mapM icode xs
  value    = vcase (mapM value)
--   icode []       = icode0'
--   icode (x : xs) = icode2' x xs
--   value = vcase valu where valu []      = valu0 []
--                            valu [x, xs] = valu2 (:) x xs
--                            valu _       = malformed

instance (Ord a, Ord b, EmbPrj a, EmbPrj b) => EmbPrj (BiMap a b) where
  icod_ m = icode (BiMap.toList m)
  value m = BiMap.fromList <$> value m

instance (Ord a, EmbPrj a, EmbPrj b) => EmbPrj (Map a b) where
  icod_ m = icode (Map.toList m)
  value m = Map.fromList `fmap` value m

instance (Ord a, EmbPrj a) => EmbPrj (Set a) where
  icod_ s = icode (Set.toList s)
  value s = Set.fromList `fmap` value s

instance EmbPrj P.Interval where
  icod_ (P.Interval p q) = icode2' p q
  value = vcase valu where valu [p, q] = valu2 P.Interval p q
                           valu _      = malformed

instance EmbPrj Range where
  icod_ (P.Range is) = icode1' is
  value = vcase valu where valu [is] = valu1 P.Range is
                           valu _    = malformed

instance EmbPrj HR.Range where
  icod_ (HR.Range a b) = icode2' a b
  value = vcase valu where valu [a, b] = valu2 HR.Range a b
                           valu _      = malformed

instance EmbPrj C.Name where
  icod_ (C.NoName a b) = icode2 0 a b
  icod_ (C.Name r xs)  = icode2' r xs
  value = vcase valu where valu [0, a, b] = valu2 C.NoName a b
                           valu [r, xs]   = valu2 C.Name   r xs
                           valu _         = malformed

instance EmbPrj NamePart where
  icod_ Hole   = icode0'
  icod_ (Id a) = icode1' a
  value = vcase valu where valu []  = valu0 Hole
                           valu [a] = valu1 Id a
                           valu _   = malformed

instance EmbPrj C.QName where
  icod_ (Qual    a b) = icode2' a b
  icod_ (C.QName a  ) = icode1' a
  value = vcase valu where valu [a, b] = valu2 Qual    a b
                           valu [a]    = valu1 C.QName a
                           valu _      = malformed

instance EmbPrj Scope where
  icod_ (Scope a b c d e) = icode5' a b c d e
  value = vcase valu where valu [a, b, c, d, e] = valu5 Scope a b c d e
                           valu _               = malformed

instance EmbPrj NameSpaceId where
  icod_ PublicNS        = icode0'
  icod_ PrivateNS       = icode0 1
  icod_ ImportedNS      = icode0 2
  icod_ OnlyQualifiedNS = icode0 3
  value = vcase valu where valu []  = valu0 PublicNS
                           valu [1] = valu0 PrivateNS
                           valu [2] = valu0 ImportedNS
                           valu [3] = valu0 OnlyQualifiedNS
                           valu _   = malformed

instance EmbPrj Access where
  icod_ PrivateAccess = icode0 0
  icod_ PublicAccess  = icode0'
  icod_ OnlyQualified = icode0 2
  value = vcase valu where valu [0] = valu0 PrivateAccess
                           valu []  = valu0 PublicAccess
                           valu [2] = valu0 OnlyQualified
                           valu _   = malformed

instance EmbPrj NameSpace where
  icod_ (NameSpace a b) = icode2' a b
  value = vcase valu where valu [a, b] = valu2 NameSpace a b
                           valu _      = malformed

instance EmbPrj WhyInScope where
  icod_ Defined       = icode0'
  icod_ (Opened a b)  = icode2 0 a b
  icod_ (Applied a b) = icode2 1 a b
  value = vcase valu where valu []        = valu0 Defined
                           valu [0, a, b] = valu2 Opened a b
                           valu [1, a, b] = valu2 Applied a b
                           valu _         = malformed

instance EmbPrj AbstractName where
  icod_ (AbsName a b c) = icode3' a b c
  value = vcase valu where valu [a, b, c] = valu3 AbsName a b c
                           valu _         = malformed

instance EmbPrj AbstractModule where
  icod_ (AbsModule a b) = icode2' a b
  value = vcase valu where valu [a, b] = valu2 AbsModule a b
                           valu _      = malformed

instance EmbPrj KindOfName where
  icod_ DefName        = icode0'
  icod_ ConName        = icode0 1
  icod_ FldName        = icode0 2
  icod_ PatternSynName = icode0 3
  icod_ QuotableName   = icode0 4
  icod_ MacroName      = icode0 5
  value = vcase valu where valu []  = valu0 DefName
                           valu [1] = valu0 ConName
                           valu [2] = valu0 FldName
                           valu [3] = valu0 PatternSynName
                           valu [4] = valu0 QuotableName
                           valu [5] = valu0 MacroName
                           valu _   = malformed

instance EmbPrj Agda.Syntax.Fixity.Associativity where
  icod_ LeftAssoc  = icode0'
  icod_ RightAssoc = icode0 1
  icod_ NonAssoc   = icode0 2
  value = vcase valu where valu []  = valu0 LeftAssoc
                           valu [1] = valu0 RightAssoc
                           valu [2] = valu0 NonAssoc
                           valu _   = malformed

instance EmbPrj Agda.Syntax.Fixity.PrecedenceLevel where
  icod_ Unrelated   = icode0'
  icod_ (Related a) = icode1' a
  value = vcase valu where valu []  = valu0 Unrelated
                           valu [a] = valu1 Related a
                           valu _   = malformed

instance EmbPrj Agda.Syntax.Fixity.Fixity where
  icod_ (Fixity a b c) = icode3' a b c
  value = vcase valu where valu [a, b, c] = valu3 Fixity a b c
                           valu _         = malformed

instance EmbPrj Agda.Syntax.Fixity.Fixity' where
  icod_ (Fixity' a b) = icode2' a b
  value = vcase valu where valu [a,b] = valu2 Fixity' a b
                           valu _ = malformed

instance EmbPrj GenPart where
  icod_ (BindHole a)   = icode1 0 a
  icod_ (NormalHole a) = icode1 1 a
  icod_ (WildHole a)   = icode1 2 a
  icod_ (IdPart a)     = icode1' a
  value = vcase valu where valu [0, a] = valu1 BindHole a
                           valu [1, a] = valu1 NormalHole a
                           valu [2, a] = valu1 WildHole a
                           valu [a]    = valu1 IdPart a
                           valu _      = malformed

instance EmbPrj A.QName where
  icod_ n@(A.QName a b) = icodeMemo qnameD qnameC (qnameId n) $ icode2' a b
  value = vcase valu where valu [a, b] = valu2 A.QName a b
                           valu _      = malformed

instance EmbPrj A.AmbiguousQName where
  icod_ (A.AmbQ a) = icode a
  value n = A.AmbQ `fmap` value n

instance EmbPrj A.ModuleName where
  icod_ (A.MName a) = icode a
  value n = A.MName `fmap` value n

instance EmbPrj A.Name where
  icod_ (A.Name a b c d) = icodeMemo nameD nameC a $ icode4' a b c d
  value = vcase valu where valu [a, b, c, d] = valu4 A.Name a b c d
                           valu _            = malformed

instance EmbPrj a => EmbPrj (C.FieldAssignment' a) where
  icod_ (C.FieldAssignment a b) = icode2' a b
  value = vcase valu where valu [a, b] = valu2 C.FieldAssignment a b
                           valu _      = malformed

instance (EmbPrj s, EmbPrj t) => EmbPrj (Named s t) where
  icod_ (Named a b) = icode2' a b
  value = vcase valu where valu [a, b] = valu2 Named a b
                           valu _      = malformed

instance EmbPrj a => EmbPrj (Ranged a) where
  icod_ (Ranged r x) = icode2' r x
  value = vcase valu where valu [r, x] = valu2 Ranged r x
                           valu _      = malformed

instance EmbPrj LocalVar where
  icod_ (LocalVar a)      = icode1' a
  icod_ (ShadowedVar a b) = icode2' a b
  value = vcase valu where valu [a]    = valu1 LocalVar a
                           valu [a, b] = valu2 ShadowedVar a b
                           valu _      = malformed

-- Only used for pattern synonyms
instance EmbPrj A.Expr where
  icod_ (A.Var n)               = icode1 0 n
  icod_ (A.Def n)               = icode1 1 n
  icod_ (A.Con ns)              = icode1 2 ns
  icod_ (A.Lit l)               = icode1 3 l
  icod_ (A.QuestionMark{})      = icode0 4
  icod_ (A.Underscore _)        = icode0 5
  icod_ (A.App _ a b)           = icode2 6 a b
  icod_ (A.WithApp _ a b)       = icode2 7 a b
  icod_ (A.Lam  _ a b)          = icode2 8 a b
  icod_ (A.AbsurdLam _ a)       = icode1 9 a
  icod_ (A.ExtendedLam _ _ _ _) = __IMPOSSIBLE__
  icod_ (A.Pi   _ a b)          = icode2 11 a b
  icod_ (A.Fun  _ a b)          = icode2 12 a b
  icod_ (A.Set  _ a)            = icode1 13 a
  icod_ (A.Prop _)              = icode0 14
  icod_ (A.Let  _ _ _)          = __IMPOSSIBLE__
  icod_ (A.ETel{})              = __IMPOSSIBLE__
  icod_ (A.Rec  _ a)            = icode1 17 a
  icod_ (A.RecUpdate _ a b)     = icode2 18 a b
  -- Andreas, 2015-07-15, drop scopes embedded in expressions.
  -- As expressions are not @unScope@d before serialization,
  -- this case is not __IMPOSSIBLE__.
  icod_ (A.ScopedExpr a b)      = icod_ b -- WAS: icode2 19 a b
  icod_ (A.QuoteGoal _ a b)     = icode2 20 a b
  icod_ (A.QuoteContext _)      = icode0 21
  icod_ (A.Quote _)             = icode0 22
  icod_ (A.QuoteTerm _)         = icode0 23
  icod_ (A.Unquote _)           = icode0 24
  icod_ (A.Tactic _ _ _ _)      = __IMPOSSIBLE__
  icod_ (A.DontCare a)          = icode1 25 a
  icod_ (A.PatternSyn a)        = icode1 26 a
  icod_ (A.Proj a)              = icode1 27 a
  icod_ (A.Macro a)             = icode1 28 a

  value = vcase valu
    where
      valu [0, a]     = valu1 A.Var a
      valu [1, a]     = valu1 A.Def a
      valu [2, a]     = valu1 A.Con a
      valu [3, a]     = valu1 A.Lit a
      valu [4]        = valu0 (A.QuestionMark emptyMetaInfo 0)
      valu [5]        = valu0 (A.Underscore emptyMetaInfo)
      valu [6, a, b]  = valu2 (A.App i) a b
      valu [7, a, b]  = valu2 (A.WithApp i) a b
      valu [8, a, b]  = valu2 (A.Lam i) a b
      valu [9, a]     = valu1 (A.AbsurdLam i) a
      valu [11, a, b] = valu2 (A.Pi i) a b
      valu [12, a, b] = valu2 (A.Fun i) a b
      valu [13, a]    = valu1 (A.Set i) a
      valu [14]       = valu0 (A.Prop i)
      valu [17, a]    = valu1 (A.Rec i) a
      valu [18, a, b] = valu2 (A.RecUpdate i) a b
      -- valu [19, a, b] = valu2 A.ScopedExpr a b
      valu [20, a, b] = valu2 (A.QuoteGoal i) a b
      valu [21]       = valu0 (A.QuoteContext i)
      valu [22]       = valu0 (A.Quote i)
      valu [23]       = valu0 (A.QuoteTerm i)
      valu [24]       = valu0 (A.Unquote i)
      valu [25, a]    = valu1 A.DontCare a
      valu [26, a]    = valu1 A.PatternSyn a
      valu [27, a]    = valu1 A.Proj a
      valu [28, a]    = valu1 A.Macro a
      valu _          = malformed

      i = ExprRange noRange

instance EmbPrj ConPatInfo where
  icod_ (ConPatInfo a _) = icod_ a
  value a = flip ConPatInfo patNoRange <$> value a

instance EmbPrj A.Pattern where
  icod_ (A.VarP a)            = icode1 0 a
  icod_ (A.ConP a b c)        = icode3 1 a b c
  icod_ (A.DefP _ a b)        = icode2 2 a b
  icod_ (A.WildP _)           = icode0 3
  icod_ (A.AsP _ a b)         = icode2 4 a b
  icod_ (A.DotP _ a)          = icode1 5 a
  icod_ (A.AbsurdP _)         = icode0 6
  icod_ (A.LitP a)            = icode1 7 a
  icod_ (A.PatternSynP _ a b) = icode2 9 a b
  icod_ (A.RecP _ a)          = icode1 10 a

  value = vcase valu
    where
     valu [0, a]    = valu1 A.VarP a
     valu [1, a, b, c] = valu3 A.ConP a b c
     valu [2, a, b] = valu2 (A.DefP i) a b
     valu [3]       = valu0 (A.WildP i)
     valu [4, a, b] = valu2 (A.AsP i) a b
     valu [5, a]    = valu1 (A.DotP i) a
     valu [6]       = valu0 (A.AbsurdP i)
     valu [7, a]    = valu1 (A.LitP) a
     valu [9, a, b] = valu2 (A.PatternSynP i) a b
     valu [10, a]   = valu1 (A.RecP i) a
     valu _         = malformed

     i  = patNoRange

instance EmbPrj A.LamBinding where
  icod_ (A.DomainFree i e) = icode2 0 i e
  icod_ (A.DomainFull a)   = icode1 1 a

  value = vcase valu where valu [0, i, e] = valu2 A.DomainFree i e
                           valu [1, a]    = valu1 A.DomainFull a
                           valu _         = malformed

instance EmbPrj A.LetBinding where
  icod_ (A.LetBind _ a b c d)  = icode4 0 a b c d
  icod_ (A.LetPatBind _ a b )  = icode2 1 a b
  icod_ (A.LetApply _ _ _ _ _) = icode0 2
  icod_ (A.LetOpen _ _)        = icode0 2

  value = vcase valu
    where
      valu [0, a, b, c, d] = valu4 (A.LetBind (LetRange noRange)) a b c d
      valu [1, a, b]       = valu2 (A.LetPatBind (LetRange noRange)) a b
      valu [2]             = throwError $ NotSupported
                                 "importing pattern synonym containing let module"
      valu _               = malformed

instance EmbPrj A.TypedBindings where
  icod_ (A.TypedBindings a b) = icode2' a b

  value = vcase valu where valu [a, b] = valu2 A.TypedBindings a b
                           valu _      = malformed

instance EmbPrj A.TypedBinding where
  icod_ (A.TBind a b c) = icode3 0 a b c
  icod_ (A.TLet a b)    = icode2 1 a b

  value = vcase valu where valu [0, a, b, c] = valu3 A.TBind a b c
                           valu [1, a, b]    = valu2 A.TLet a b
                           valu _            = malformed

instance EmbPrj c => EmbPrj (Common.ArgInfo c) where
  icod_ (ArgInfo h r cs) = icode3' h r cs

  value = vcase valu where valu [h, r, cs] = valu3 ArgInfo h r cs
                           valu _          = malformed

instance EmbPrj NameId where
  icod_ (NameId a b) = icode2' a b
  value = vcase valu where valu [a, b] = valu2 NameId a b
                           valu _      = malformed

instance EmbPrj Signature where
  icod_ (Sig a b c) = icode3' a b c
  value = vcase valu where valu [a, b, c] = valu3 Sig a b c
                           valu _ = malformed

instance (Eq k, Hashable k, EmbPrj k, EmbPrj v) => EmbPrj (HashMap k v) where
  icod_ m = icode (HMap.toList m)
  value m = HMap.fromList `fmap` value m

instance EmbPrj Section where
  icod_ (Section a b) = icode2' a b
  value = vcase valu where valu [a, b] = valu2 Section a b
                           valu _      = malformed

instance EmbPrj Telescope where
  icod_ EmptyTel        = icode0'
  icod_ (ExtendTel a b) = icode2' a b
  value = vcase valu where valu []     = valu0 EmptyTel
                           valu [a, b] = valu2 ExtendTel a b
                           valu _      = malformed

instance EmbPrj Permutation where
  icod_ (Perm a b) = icode2' a b
  value = vcase valu where valu [a, b] = valu2 Perm a b
                           valu _      = malformed

instance EmbPrj a => EmbPrj (Drop a) where
  icod_ (Drop a b) = icode2' a b
  value = vcase valu where valu [a, b] = valu2 Drop a b
                           valu _      = malformed

instance EmbPrj a => EmbPrj (Elim' a) where
  icod_ (Apply a) = icode1' a
  icod_ (Proj  a) = icode1 0 a
  value = vcase valu where valu [a]    = valu1 Apply a
                           valu [0, a] = valu1 Proj a
                           valu _      = malformed

instance EmbPrj a => EmbPrj (WithHiding a) where
  icod_ (WithHiding a b) = icode2' a b
  value = vcase valu where valu [a, b] = valu2 WithHiding a b
                           valu _      = malformed

instance (EmbPrj a, EmbPrj c) => EmbPrj (Common.Arg c a) where
  icod_ (Arg i e) = icode2' i e
  value = vcase valu where valu [i, e] = valu2 Arg i e
                           valu _      = malformed

instance (EmbPrj a, EmbPrj c) => EmbPrj (Common.Dom c a) where
  icod_ (Dom i e) = icode2' i e
  value = vcase valu where valu [i, e] = valu2 Dom i e
                           valu _      = malformed

instance EmbPrj Common.Induction where
  icod_ Inductive   = icode0'
  icod_ CoInductive = icode0 1
  value = vcase valu where valu []  = valu0 Inductive
                           valu [1] = valu0 CoInductive
                           valu _   = malformed

instance EmbPrj Common.Hiding where
  icod_ Hidden    = return 0
  icod_ NotHidden = return 1
  icod_ Instance  = return 2
  value 0 = return Hidden
  value 1 = return NotHidden
  value 2 = return Instance
  value _ = malformed

instance EmbPrj Common.Relevance where
  icod_ Relevant       = return 0
  icod_ Irrelevant     = return 1
  icod_ (Forced Small) = return 2
  icod_ (Forced Big)   = return 3
  icod_ NonStrict      = return 4
  icod_ UnusedArg      = return 5
  value 0 = return Relevant
  value 1 = return Irrelevant
  value 2 = return (Forced Small)
  value 3 = return (Forced Big)
  value 4 = return NonStrict
  value 5 = return UnusedArg
  value _ = malformed

-- instance EmbPrj Common.Relevance where
--   icod_ Relevant   = icode0'
--   icod_ Irrelevant = icode0 1
--   icod_ (Forced Small) = icode0 2
--   icod_ (Forced Big)   = icode0 5
--   icod_ NonStrict  = icode0 3
--   icod_ UnusedArg  = icode0 4
--   value = vcase valu where valu []  = valu0 Relevant
--                            valu [1] = valu0 Irrelevant
--                            valu [2] = valu0 (Forced Small)
--                            valu [5] = valu0 (Forced Big)
--                            valu [3] = valu0 NonStrict
--                            valu [4] = valu0 UnusedArg
--                            valu _   = malformed

instance EmbPrj I.ConHead where
  icod_ (ConHead a b c) = icode3' a b c
  value = vcase valu where valu [a, b, c] = valu3 ConHead a b c
                           valu _         = malformed

instance (EmbPrj a) => EmbPrj (I.Type' a) where
  icod_ (El a b) = icode2' a b
  value = vcase valu where valu [a, b] = valu2 El a b
                           valu _      = malformed

instance (EmbPrj a) => EmbPrj (I.Abs a) where
  icod_ (NoAbs a b) = icode2 0 a b
  icod_ (Abs a b)   = icode2' a b
  value = vcase valu where valu [a, b]    = valu2 Abs a b
                           valu [0, a, b] = valu2 NoAbs a b
                           valu _         = malformed

instance EmbPrj I.Term where
  icod_ (Var     a []) = icode1' a
  icod_ (Var      a b) = icode2 0 a b
  icod_ (Lam      a b) = icode2 1 a b
  icod_ (Lit      a  ) = icode1 2 a
  icod_ (Def      a b) = icode2 3 a b
  icod_ (Con      a b) = icode2 4 a b
  icod_ (Pi       a b) = icode2 5 a b
  icod_ (Sort     a  ) = icode1 7 a
  icod_ (MetaV    a b) = __IMPOSSIBLE__
  icod_ (DontCare a  ) = icode1 8 a
  icod_ (Level    a  ) = icode1 9 a
  icod_ (Shared p)     = icodeMemo termD termC p $ icode (derefPtr p)

  value r = vcase valu' r
    where
      valu' xs = gets mkShared <*> valu xs
      valu [a]       = valu1 var   a
      valu [0, a, b] = valu2 Var   a b
      valu [1, a, b] = valu2 Lam   a b
      valu [2, a]    = valu1 Lit   a
      valu [3, a, b] = valu2 Def   a b
      valu [4, a, b] = valu2 Con   a b
      valu [5, a, b] = valu2 Pi    a b
      valu [7, a]    = valu1 Sort  a
      valu [8, a]    = valu1 DontCare a
      valu [9, a]    = valu1 Level a
      valu _         = malformed

instance EmbPrj Level where
  icod_ (Max a) = icode1' a
  value = vcase valu where valu [a] = valu1 Max a
                           valu _   = malformed

instance EmbPrj PlusLevel where
  icod_ (ClosedLevel a) = icode1' a
  icod_ (Plus a b)      = icode2' a b
  value = vcase valu where valu [a]    = valu1 ClosedLevel a
                           valu [a, b] = valu2 Plus a b
                           valu _      = malformed

instance EmbPrj LevelAtom where
  icod_ (NeutralLevel _ a) = icode1' a
  icod_ (UnreducedLevel a) = icode1 1 a
  icod_ MetaLevel{}        = __IMPOSSIBLE__
  icod_ BlockedLevel{}     = __IMPOSSIBLE__
  value = vcase valu where
    valu [a]    = valu1 UnreducedLevel a -- we forget that we are a NeutralLevel,
                                         -- since we do not want do (de)serialize
                                         -- the reason for neutrality
    valu [1, a] = valu1 UnreducedLevel a
    valu _      = malformed

instance EmbPrj I.Sort where
  icod_ (Type  a  ) = icode1' a
  icod_ Prop        = icode1 1 ()
  icod_ SizeUniv    = icode1 3 ()
  icod_ Inf         = icode1 4 ()
  icod_ (DLub a b)  = __IMPOSSIBLE__
  value = vcase valu where valu [a]    = valu1 Type  a
                           valu [1, _] = valu0 Prop
                           valu [3, _] = valu0 SizeUniv
                           valu [4, _] = valu0 Inf
                           valu _      = malformed

instance EmbPrj Agda.Syntax.Literal.Literal where
  icod_ (LitInt    a b) = icode2' a b
  icod_ (LitFloat  a b) = icode2 1 a b
  icod_ (LitString a b) = icode2 2 a b
  icod_ (LitChar   a b) = icode2 3 a b
  icod_ (LitQName  a b) = icode2 5 a b
  value = vcase valu where valu [a, b]    = valu2 LitInt    a b
                           valu [1, a, b] = valu2 LitFloat  a b
                           valu [2, a, b] = valu2 LitString a b
                           valu [3, a, b] = valu2 LitChar   a b
                           valu [5, a, b] = valu2 LitQName  a b
                           valu _         = malformed

instance EmbPrj DisplayForm where
  icod_ (Display a b c) = icode3' a b c
  value = vcase valu where valu [a, b, c] = valu3 Display a b c
                           valu _         = malformed

instance EmbPrj a => EmbPrj (Open a) where
  icod_ (OpenThing a b) = icode2' a b
  value = vcase valu where valu [a, b] = valu2 OpenThing a b
                           valu _      = malformed

instance EmbPrj CtxId where
  icod_ (CtxId a) = icode a
  value n = CtxId `fmap` value n

instance EmbPrj DisplayTerm where
  icod_ (DTerm    a  ) = icode1' a
  icod_ (DDot     a  ) = icode1 1 a
  icod_ (DCon     a b) = icode2 2 a b
  icod_ (DDef     a b) = icode2 3 a b
  icod_ (DWithApp a b c) = icode3 4 a b c
  value = vcase valu where valu [a]       = valu1 DTerm a
                           valu [1, a]    = valu1 DDot a
                           valu [2, a, b] = valu2 DCon a b
                           valu [3, a, b] = valu2 DDef a b
                           valu [4, a, b, c] = valu3 DWithApp a b c
                           valu _         = malformed

instance EmbPrj MutualId where
  icod_ (MutId a) = icode a
  value n = MutId `fmap` value n

instance EmbPrj Definition where
  icod_ (Defn rel a b c d e f g h i) = icode10' rel a (P.killRange b) c d e f g h i
  value = vcase valu where valu [rel, a, b, c, d, e, f, g, h, i] = valu10 Defn rel a b c d e f g h i
                           valu _ = malformed

instance EmbPrj NLPat where
  icod_ (PVar a)   = icode1 0 a
  icod_ (PWild)    = icode0 1
  icod_ (PDef a b) = icode2 2 a b
  icod_ (PLam a b) = icode2 3 a b
  icod_ (PPi a b)  = icode2 4 a b
  icod_ (PBoundVar a b) = icode2 5 a b
  icod_ (PTerm a)  = icode1 6 a
  value = vcase valu where valu [0, a]    = valu1 PVar a
                           valu [1]       = valu0 PWild
                           valu [2, a, b] = valu2 PDef a b
                           valu [3, a, b] = valu2 PLam a b
                           valu [4, a, b] = valu2 PPi a b
                           valu [5, a, b] = valu2 PBoundVar a b
                           valu [6, a]    = valu1 PTerm a
                           valu _         = malformed

instance EmbPrj RewriteRule where
  icod_ (RewriteRule a b c d e) = icode5' a b c d e
  value = vcase valu where valu [a, b, c, d, e] = valu5 RewriteRule a b c d e
                           valu _               = malformed


instance EmbPrj Projection where
  icod_ (Projection a b c d e) = icode5' a b c d e
  value = vcase valu where valu [a, b, c, d, e] = valu5 Projection a b c d e
                           valu _               = malformed

instance EmbPrj HaskellExport where
  icod_ (HsExport a b) = icode2' a b
  value = vcase valu where
    valu [a,b] = valu2 HsExport a b
    valu _ = malformed

instance EmbPrj HaskellRepresentation where
  icod_ (HsType a)   = icode1' a
  icod_ (HsDefn a b) = icode2' a b

  value = vcase valu where
    valu [a]    = valu1 HsType a
    valu [a, b] = valu2 HsDefn a b
    valu _      = malformed

instance EmbPrj JS.Exp where
  icod_ (JS.Self)         = icode0 0
  icod_ (JS.Local i)      = icode1 1 i
  icod_ (JS.Global i)     = icode1 2 i
  icod_ (JS.Undefined)    = icode0 3
  icod_ (JS.String s)     = icode1 4 s
  icod_ (JS.Char c)       = icode1 5 c
  icod_ (JS.Integer n)    = icode1 6 n
  icod_ (JS.Double d)     = icode1 7 d
  icod_ (JS.Lambda n e)   = icode2 8 n e
  icod_ (JS.Object o)     = icode1 9 o
  icod_ (JS.Apply e es)   = icode2 10 e es
  icod_ (JS.Lookup e l)   = icode2 11 e l
  icod_ (JS.If e f g)     = icode3 12 e f g
  icod_ (JS.BinOp e op f) = icode3 13 e op f
  icod_ (JS.PreOp op e)   = icode2 14 op e
  icod_ (JS.Const i)      = icode1 15 i
  value = vcase valu where valu [0]           = valu0 JS.Self
                           valu [1,  a]       = valu1 JS.Local a
                           valu [2,  a]       = valu1 JS.Global a
                           valu [3]           = valu0 JS.Undefined
                           valu [4,  a]       = valu1 JS.String a
                           valu [5,  a]       = valu1 JS.Char a
                           valu [6,  a]       = valu1 JS.Integer a
                           valu [7,  a]       = valu1 JS.Double a
                           valu [8,  a, b]    = valu2 JS.Lambda a b
                           valu [9,  a]       = valu1 JS.Object a
                           valu [10, a, b]    = valu2 JS.Apply a b
                           valu [11, a, b]    = valu2 JS.Lookup a b
                           valu [12, a, b, c] = valu3 JS.If a b c
                           valu [13, a, b, c] = valu3 JS.BinOp a b c
                           valu [14, a, b]    = valu2 JS.PreOp a b
                           valu [15, a]       = valu1 JS.Const a
                           valu _             = malformed

instance EmbPrj JS.LocalId where
  icod_ (JS.LocalId l) = icode l
  value n = JS.LocalId `fmap` value n

instance EmbPrj JS.GlobalId where
  icod_ (JS.GlobalId l) = icode l
  value n = JS.GlobalId `fmap` value n

instance EmbPrj JS.MemberId where
  icod_ (JS.MemberId l) = icode l
  value n = JS.MemberId `fmap` value n

instance EmbPrj CoreRepresentation where
  icod_ (CrDefn a)   = icode1 1 a
  icod_ (CrType a)   = icode1 2 a
  icod_ (CrConstr a) = icode1 3 a

  value = vcase valu where
    valu [1, a] = valu1 CrDefn a
    valu [2, a] = valu1 CrType a
    valu [3, a] = valu1 CrConstr a
    valu _      = malformed

instance EmbPrj CR.CoreType where
  icod_ (CR.CTMagic a) = icode1 1 a
  icod_ (CR.CTNormal a)  = icode1 2 a
  value = vcase valu where
    valu [1, a]    = valu1 CR.CTMagic a
    valu [2, a]    = valu1 CR.CTNormal a
    valu _         = malformed

instance EmbPrj CR.CoreConstr where
  icod_ (CR.CCMagic a b) = icode2 1 a b
  icod_ (CR.CCNormal a b c) = icode3 2 a b c
  value = vcase valu where
    valu [1, a, b]    = valu2 CR.CCMagic a b
    valu [2, a, b, c] = valu3 CR.CCNormal a b c
    valu _            = malformed

instance EmbPrj CR.HsName where
  icod_ = icode . B.runPut . UHCB.serialize
  value n = value n >>= return . (B.runGet UHCB.unserialize)

instance EmbPrj Polarity where
  icod_ Covariant     = return 0
  icod_ Contravariant = return 1
  icod_ Invariant     = return 2
  icod_ Nonvariant    = return 3

  value 0 = return Covariant
  value 1 = return Contravariant
  value 2 = return Invariant
  value 3 = return Nonvariant
  value _  = malformed

-- instance EmbPrj Polarity where
--   icod_ Covariant     = icode0'
--   icod_ Contravariant = icode0 1
--   icod_ Invariant     = icode0 2
--   icod_ Nonvariant    = icode0 3

--   value = vcase valu where
--     valu []  = valu0 Covariant
--     valu [1] = valu0 Contravariant
--     valu [2] = valu0 Invariant
--     valu [3] = valu0 Nonvariant
--     valu _   = malformed

instance EmbPrj Occurrence where
  icod_ StrictPos = return 0
  icod_ Mixed     = return 1
  icod_ Unused    = return 2
  icod_ GuardPos  = return 3
  icod_ JustPos   = return 4
  icod_ JustNeg   = return 5

  value 0 = return StrictPos
  value 1 = return Mixed
  value 2 = return Unused
  value 3 = return GuardPos
  value 4 = return JustPos
  value 5 = return JustNeg
  value _ = malformed

-- instance EmbPrj Occurrence where
--   icod_ StrictPos = icode0'
--   icod_ Mixed     = icode0 1
--   icod_ Unused    = icode0 2
--   icod_ GuardPos  = icode0 3
--   icod_ JustPos   = icode0 4
--   icod_ JustNeg   = icode0 5

--   value = vcase valu where
--     valu []  = valu0 StrictPos
--     valu [1] = valu0 Mixed
--     valu [2] = valu0 Unused
--     valu [3] = valu0 GuardPos
--     valu [4] = valu0 JustPos
--     valu [5] = valu0 JustNeg
--     valu _   = malformed

instance EmbPrj CompiledRepresentation where
  icod_ (CompiledRep a b c d e) = icode5' a b c d e
  value = vcase valu where valu [a, b, c, d, e] = valu5 CompiledRep a b c d e
                           valu _         = malformed

instance EmbPrj EtaEquality where
  icod_ (Specified a) = icode1 0 a
  icod_ (Inferred a)  = icode1 1 a
  value = vcase valu where
    valu [0,a] = valu1 Specified a
    valu [1,a] = valu1 Inferred a
    valu _     = malformed

instance EmbPrj Defn where
  icod_ Axiom                                   = icode0 0
  icod_ (Function    a b c d e f g h i j k l m n) = icode14 1 a b c d e f g h i j k l m n
  icod_ (Datatype    a b c d e f g h i j)       = icode10 2 a b c d e f g h i j
  icod_ (Record      a b c d e f g h i j k l)   = icode12 3 a b c d e f g h i j k l
  icod_ (Constructor a b c d e)                 = icode5 4 a b c d e
  icod_ (Primitive   a b c d)                   = icode4 5 a b c d
  value = vcase valu where
    valu [0]                                     = valu0 Axiom
    valu [1, a, b, c, d, e, f, g, h, i, j, k, l, m, n] = valu14 Function a b c d e f g h i j k l m n
    valu [2, a, b, c, d, e, f, g, h, i, j]       = valu10 Datatype a b c d e f g h i j
    valu [3, a, b, c, d, e, f, g, h, i, j, k, l] = valu12 Record  a b c d e f g h i j k l
    valu [4, a, b, c, d, e]                      = valu5 Constructor a b c d e
    valu [5, a, b, c, d]                         = valu4 Primitive   a b c d
    valu _                                       = malformed

instance EmbPrj a => EmbPrj (WithArity a) where
  icod_ (WithArity a b) = icode2' a b

  value = vcase valu where
    valu [a, b] = valu2 WithArity a b
    valu _      = malformed

instance EmbPrj a => EmbPrj (Case a) where
  icod_ (Branches a b c d) = icode4' a b c d

  value = vcase valu where
    valu [a, b, c, d] = valu4 Branches a b c d
    valu _            = malformed

instance EmbPrj CompiledClauses where
  icod_ Fail       = icode0'
  icod_ (Done a b) = icode2' a (P.killRange b)
  icod_ (Case a b) = icode2 2 a b

  value = vcase valu where
    valu []        = valu0 Fail
    valu [a, b]    = valu2 Done a b
    valu [2, a, b] = valu2 Case a b
    valu _         = malformed

instance EmbPrj FunctionInverse where
  icod_ NotInjective = icode0'
  icod_ (Inverse a)  = icode1' a
  value = vcase valu where valu []  = valu0 NotInjective
                           valu [a] = valu1 Inverse a
                           valu _   = malformed

instance EmbPrj TermHead where
  icod_ SortHead     = icode0'
  icod_ PiHead       = icode0 1
  icod_ (ConsHead a) = icode1 2 a
  value = vcase valu where valu []     = valu0 SortHead
                           valu [1]    = valu0 PiHead
                           valu [2, a] = valu1 ConsHead a
                           valu _      = malformed

instance EmbPrj Common.IsAbstract where
  icod_ AbstractDef = icode0 0
  icod_ ConcreteDef = icode0'
  value = vcase valu where valu [0] = valu0 AbstractDef
                           valu []  = valu0 ConcreteDef
                           valu _   = malformed

instance EmbPrj I.Clause where
  icod_ (Clause a b c d e f g) = icode7' a b c d e f g
  value = vcase valu where valu [a, b, c, d, e, f, g] = valu7 Clause a b c d e f g
                           valu _                     = malformed

instance EmbPrj I.ClauseBody where
  icod_ (Body   a) = icode1 0 a
  icod_ (Bind   a) = icode1' a
  icod_ NoBody     = icode0'
  value = vcase valu where valu [0, a] = valu1 Body   a
                           valu [a]    = valu1 Bind   a
                           valu []     = valu0 NoBody
                           valu _      = malformed

instance EmbPrj Delayed where
  icod_ Delayed    = icode0 0
  icod_ NotDelayed = icode0'
  value = vcase valu where valu [0] = valu0 Delayed
                           valu []  = valu0 NotDelayed
                           valu _   = malformed

instance EmbPrj I.ConPatternInfo where
  icod_ (ConPatternInfo a b) = icode2' a b
  value = vcase valu where valu [a, b] = valu2 ConPatternInfo a b
                           valu _      = malformed

instance EmbPrj ConPOrigin where
  icod_ ConPImplicit = return 0
  icod_ ConPCon      = return 1
  icod_ ConPRec      = return 2
  value 0 = return ConPImplicit
  value 1 = return ConPCon
  value 2 = return ConPRec
  value _ = malformed

instance EmbPrj I.Pattern where
  icod_ (VarP a    ) = icode1' a
  icod_ (ConP a b c) = icode3' a b c
  icod_ (LitP a    ) = icode1 2 a
  icod_ (DotP a    ) = icode1 3 a
  icod_ (ProjP a   ) = icode1 4 a
  value = vcase valu where valu [a]       = valu1 VarP a
                           valu [a, b, c] = valu3 ConP a b c
                           valu [2, a]    = valu1 LitP a
                           valu [3, a]    = valu1 DotP a
                           valu [4, a]    = valu1 ProjP a
                           valu _         = malformed

instance EmbPrj a => EmbPrj (Builtin a) where
  icod_ (Prim    a) = icode1' a
  icod_ (Builtin a) = icode1 1 a
  value = vcase valu where valu [a]    = valu1 Prim    a
                           valu [1, a] = valu1 Builtin a
                           valu _      = malformed

instance EmbPrj HP.NameKind where
  icod_ HP.Bound           = icode0'
  icod_ (HP.Constructor a) = icode1 1 a
  icod_ HP.Datatype        = icode0 2
  icod_ HP.Field           = icode0 3
  icod_ HP.Function        = icode0 4
  icod_ HP.Module          = icode0 5
  icod_ HP.Postulate       = icode0 6
  icod_ HP.Primitive       = icode0 7
  icod_ HP.Record          = icode0 8
  icod_ HP.Argument        = icode0 9
  icod_ HP.Macro           = icode0 10

  value = vcase valu where
    valu []      = valu0 HP.Bound
    valu [1 , a] = valu1 HP.Constructor a
    valu [2]     = valu0 HP.Datatype
    valu [3]     = valu0 HP.Field
    valu [4]     = valu0 HP.Function
    valu [5]     = valu0 HP.Module
    valu [6]     = valu0 HP.Postulate
    valu [7]     = valu0 HP.Primitive
    valu [8]     = valu0 HP.Record
    valu [9]     = valu0 HP.Argument
    valu [10]    = valu0 HP.Macro
    valu _       = malformed

instance EmbPrj HP.Aspect where
  icod_ HP.Comment       = icode0 0
  icod_ HP.Keyword       = icode0 1
  icod_ HP.String        = icode0 2
  icod_ HP.Number        = icode0 3
  icod_ HP.Symbol        = icode0'
  icod_ HP.PrimitiveType = icode0 5
  icod_ (HP.Name mk b)   = icode2 6 mk b

  value = vcase valu where
    valu [0]        = valu0 HP.Comment
    valu [1]        = valu0 HP.Keyword
    valu [2]        = valu0 HP.String
    valu [3]        = valu0 HP.Number
    valu []         = valu0 HP.Symbol
    valu [5]        = valu0 HP.PrimitiveType
    valu [6, mk, b] = valu2 HP.Name mk b
    valu _          = malformed

instance EmbPrj HP.OtherAspect where
  icod_ HP.Error              = icode0 0
  icod_ HP.DottedPattern      = icode0'
  icod_ HP.UnsolvedMeta       = icode0 2
  icod_ HP.TerminationProblem = icode0 3
  icod_ HP.IncompletePattern  = icode0 4
  icod_ HP.TypeChecks         = icode0 5
  icod_ HP.UnsolvedConstraint = icode0 6

  value = vcase valu where
    valu [0] = valu0 HP.Error
    valu []  = valu0 HP.DottedPattern
    valu [2] = valu0 HP.UnsolvedMeta
    valu [3] = valu0 HP.TerminationProblem
    valu [4] = valu0 HP.IncompletePattern
    valu [5] = valu0 HP.TypeChecks
    valu [6] = valu0 HP.UnsolvedConstraint
    valu _   = malformed

instance EmbPrj HP.Aspects where
  icod_ (HP.Aspects a b c d) = icode4' a b c d

  value = vcase valu where
    valu [a, b, c, d] = valu4 HP.Aspects a b c d
    valu _            = malformed

instance EmbPrj Precedence where
  icod_ TopCtx                 = icode0'
  icod_ FunctionSpaceDomainCtx = icode0 1
  icod_ (LeftOperandCtx a)     = icode1 2 a
  icod_ (RightOperandCtx a)    = icode1 3 a
  icod_ FunctionCtx            = icode0 4
  icod_ ArgumentCtx            = icode0 5
  icod_ InsideOperandCtx       = icode0 6
  icod_ WithFunCtx             = icode0 7
  icod_ WithArgCtx             = icode0 8
  icod_ DotPatternCtx          = icode0 9
  value = vcase valu
    where
    valu []     = valu0 TopCtx
    valu [1]    = valu0 FunctionSpaceDomainCtx
    valu [2, a] = valu1 LeftOperandCtx a
    valu [3, a] = valu1 RightOperandCtx a
    valu [4]    = valu0 FunctionCtx
    valu [5]    = valu0 ArgumentCtx
    valu [6]    = valu0 InsideOperandCtx
    valu [7]    = valu0 WithFunCtx
    valu [8]    = valu0 WithArgCtx
    valu [9]    = valu0 DotPatternCtx
    valu _      = malformed

instance EmbPrj ScopeInfo where
  icod_ (ScopeInfo a b c d) = icode4' a b c d
  value = vcase valu where valu [a, b, c, d] = valu4 ScopeInfo a b c d
                           valu _            = malformed

instance EmbPrj HP.CompressedFile where
  icod_ (HP.CompressedFile f) = icode1' f
  value = vcase valu
    where
    valu [f] = valu1 HP.CompressedFile f
    valu _   = malformed

instance EmbPrj Interface where
  icod_ (Interface a b c d e f g h i j k l) = icode12' a b c d e f g h i j k l
  value = vcase valu
    where
      valu [a, b, c, d, e, f, g, h, i, j, k, l] = valu12 Interface a b c d e f g h i j k l
      valu _                                    = malformed

-- This is used for the Epic compiler backend
instance EmbPrj Epic.EInterface where
  icod_ (Epic.EInterface a b c d e f g h) = icode8' a b c d e f g h
  value = vcase valu where
    valu [a, b, c, d, e, f, g, h] = valu8 Epic.EInterface a b c d e f g h
    valu _                        = malformed

instance EmbPrj Epic.InjectiveFun where
  icod_ (Epic.InjectiveFun a b) = icode2' a b
  value = vcase valu where
     valu [a,b] = valu2 Epic.InjectiveFun a b
     valu _     = malformed

instance EmbPrj Epic.Relevance where
  icod_ Epic.Irr      = icode0 0
  icod_ Epic.Rel      = icode0 1
  value = vcase valu where valu [0] = valu0 Epic.Irr
                           valu [1] = valu0 Epic.Rel
                           valu _   = malformed

instance EmbPrj Epic.Forced where
  icod_ Epic.Forced    = icode0 0
  icod_ Epic.NotForced = icode0 1
  value = vcase valu where valu [0] = valu0 Epic.Forced
                           valu [1] = valu0 Epic.NotForced
                           valu _   = malformed

instance EmbPrj Epic.Tag where
  icod_ (Epic.Tag a)     = icode1 0 a
  icod_ (Epic.PrimTag a) = icode1 1 a
  value = vcase valu
    where
    valu [0, a] = valu1 Epic.Tag a
    valu [1, a] = valu1 Epic.PrimTag a
    valu _      = malformed

-- Used by UHC backend. Will be stored in a seperate file,
-- not part of the .agdai files. Should be moved somewhere else.
instance EmbPrj UHC.AModuleInfo where
  icod_ (UHC.AModuleInfo a b c d e) = icode5' a b c d e
  value = vcase valu where
    valu [a, b, c, d, e] = valu5 UHC.AModuleInfo a b c d e
    valu _ = malformed

instance EmbPrj UHC.AModuleInterface where
  icod_ (UHC.AModuleInterface a b) = icode2' a b
  value = vcase valu where
    valu [a, b] = valu2 UHC.AModuleInterface a b
    valu _      = malformed

instance EmbPrj UHC.AConInfo where
  icod_ (UHC.AConInfo a b) = icode2' a b
  value = vcase valu where
    valu [a, b] = valu2 UHC.AConInfo a b
    valu _      = malformed

instance EmbPrj UHCA.ADataTy where
  icod_ (UHCA.ADataTy a b c d) = icode4' a b c d
  value = vcase valu where
    valu [a, b, c, d] = valu4 UHCA.ADataTy a b c d
    valu _            = malformed

instance EmbPrj UHCA.ADataCon where
  icod_ (UHCA.ADataCon a b) = icode2' a b
  value = vcase valu where
    valu [a, b] = valu2 UHCA.ADataCon a b
    valu _         = malformed

instance EmbPrj UHCA.ADataImplType where
  icod_ (UHCA.ADataImplNormal)    = icode0 0
  icod_ (UHCA.ADataImplMagic a)   = icode1 1 a
  icod_ (UHCA.ADataImplForeign)   = icode0 2
  value = vcase valu where
    valu [0]    = valu0 UHCA.ADataImplNormal
    valu [1, a] = valu1 UHCA.ADataImplMagic a
    valu [2]    = valu0 UHCA.ADataImplForeign
    valu _      = malformed

instance EmbPrj UHCN.NameMap where
  icod_ (UHCN.NameMap a b) = icode2' a b
  value = vcase valu where
    valu [a, b] = valu2 UHCN.NameMap a b
    valu _      = malformed

instance EmbPrj UHCA.CTag where
  icod_ = icode . B.runPut . UHCB.serialize
  value n = value n >>= return . (B.runGet UHCB.unserialize)

instance EmbPrj UHCN.CoreName where
  icod_ (UHCN.CoreName a b c) = icode3' a b c
  value = vcase valu where
    valu [a, b, c] = valu3 UHCN.CoreName a b c
    valu _         = malformed

instance EmbPrj UHCN.EntityType where
  icod_ UHCN.EtDatatype     = icode0 0
  icod_ UHCN.EtConstructor  = icode0 1
  icod_ UHCN.EtFunction     = icode0 2
  value = vcase valu where
    valu [0] = valu0 UHCN.EtDatatype
    valu [1] = valu0 UHCN.EtConstructor
    valu [2] = valu0 UHCN.EtFunction
    valu _   = malformed

-- Specializing icodeX leads to Warning like
-- src/full/Agda/TypeChecking/Serialise.hs:1297:1: Warning:
--     RULE left-hand side too complicated to desugar
--       case cobox_aQY5 of _ [Occ=Dead] { ghc-prim:GHC.Types.Eq# cobox ->
--       icodeX @ String $dEq_aQY3 $dHashable_aQY4
--       }
--
-- type ICodeX k
--   =  (Dict -> HashTable k Int32)
--   -> (Dict -> IORef Int32)
--   -> k -> S Int32
-- {-# SPECIALIZE icodeX :: ICodeX String  #-}
-- {-# SPECIALIZE icodeX :: ICodeX Integer #-}
-- {-# SPECIALIZE icodeX :: ICodeX Double  #-}
-- {-# SPECIALIZE icodeX :: ICodeX Node    #-}

-- Andreas, 2014-10-16 AIM XX:
-- Inlining this increases Serialization time by 10%
-- Makoto's theory: code size increase might lead to
-- instruction cache misses.
-- {-# INLINE icodeX #-}
icodeX :: (Eq k, Hashable k)
  =>  (Dict -> HashTable k Int32)
  -> (Dict -> IORef FreshAndReuse)
  -> k -> S Int32
icodeX dict counter key = do
  d <- asks dict
  c <- asks counter
  liftIO $ do
    mi <- H.lookup d key
    case mi of
      Just i  -> do
        modifyIORef' c $ over lensReuse (+1)
        return i
      Nothing -> do
        fresh <- (^.lensFresh) <$> do readModifyIORef' c $ over lensFresh (+1)
        H.insert d key fresh
        return fresh

-- Instead of inlining icodeX, we manually specialize it to
-- its four uses: Integer, String, Double, Node.
-- Not a great gain (hardly noticeable), but not harmful.

icodeInteger :: Integer -> S Int32
icodeInteger key = do
  d <- asks integerD
  c <- asks integerC
  liftIO $ do
    mi <- H.lookup d key
    case mi of
      Just i  -> do
        modifyIORef' c $ over lensReuse (+1)
        return i
      Nothing -> do
        fresh <- (^.lensFresh) <$> do readModifyIORef' c $ over lensFresh (+1)
        H.insert d key fresh
        return fresh

icodeDouble :: Double -> S Int32
icodeDouble key = do
  d <- asks doubleD
  c <- asks doubleC
  liftIO $ do
    mi <- H.lookup d key
    case mi of
      Just i  -> do
        modifyIORef' c $ over lensReuse (+1)
        return i
      Nothing -> do
        fresh <- (^.lensFresh) <$> do readModifyIORef' c $ over lensFresh (+1)
        H.insert d key fresh
        return fresh

icodeString :: String -> S Int32
icodeString key = do
  d <- asks stringD
  c <- asks stringC
  liftIO $ do
    mi <- H.lookup d key
    case mi of
      Just i  -> do
        modifyIORef' c $ over lensReuse (+1)
        return i
      Nothing -> do
        fresh <- (^.lensFresh) <$> do readModifyIORef' c $ over lensFresh (+1)
        H.insert d key fresh
        return fresh

icodeN :: Node -> S Int32
icodeN key = do
  d <- asks nodeD
  c <- asks nodeC
  liftIO $ do
    mi <- H.lookup d key
    case mi of
      Just i  -> do
        modifyIORef' c $ over lensReuse (+1)
        return i
      Nothing -> do
        fresh <- (^.lensFresh) <$> do readModifyIORef' c $ over lensFresh (+1)
        H.insert d key fresh
        return fresh

-- icodeN :: [Int32] -> S Int32
-- icodeN = icodeX nodeD nodeC

-- | @icode@ only if thing has not seen before.
icodeMemo
  :: (Eq a, Ord a, Hashable a)
  => (Dict -> HashTable a Int32)    -- ^ Memo structure for thing of key @a@.
  -> (Dict -> IORef FreshAndReuse)  -- ^ Statistics.
  -> a        -- ^ Key to the thing.
  -> S Int32  -- ^ Fallback computation to encode the thing.
  -> S Int32  -- ^ Encoded thing.
icodeMemo getDict getCounter a icodeP = do
    h  <- asks getDict
    mi <- liftIO $ H.lookup h a
    st <- asks getCounter
    case mi of
      Just i  -> liftIO $ do
        modifyIORef' st $ over lensReuse (+ 1)
        return i
      Nothing -> do
        liftIO $ modifyIORef' st $ over lensFresh (+1)
        i <- icodeP
        liftIO $ H.insert h a i
        return i

{-# INLINE vcase #-}
-- | @vcase value ix@ decodes thing represented by @ix :: Int32@
--   via the @valu@ function and stores it in 'nodeMemo'.
--   If @ix@ is present in 'nodeMemo', @valu@ is not used, but
--   the thing is read from 'nodeMemo' instead.
vcase :: forall a . EmbPrj a => (Node -> R a) -> Int32 -> R a
vcase valu = \ix -> do
    memo <- gets nodeMemo
    -- compute run-time representation of type a
    let aTyp = typeOf (undefined :: a)
    -- to introduce sharing, see if we have seen a thing
    -- represented by ix before
    maybeU <- liftIO $ H.lookup memo (ix, aTyp)
    case maybeU of
      -- yes, we have seen it before, use the version from memo
      Just (U u) -> maybe malformed return (cast u)
      -- no, it's new, so generate it via valu and insert it into memo
      Nothing    -> do
          v <- valu . (! ix) =<< gets nodeE
          liftIO $ H.insert memo (ix, aTyp) (U v)
          return v

-- Andreas, Makoto, AIM XX (2014-10-15):
-- No performance gain for INLINE here (neutral / slighly negative).
--
-- {-# INLINE icode0 #-}
-- {-# INLINE icode1 #-}
-- {-# INLINE icode2 #-}
-- {-# INLINE icode3 #-}
-- {-# INLINE icode4 #-}
-- {-# INLINE icode5 #-}
-- {-# INLINE icode6 #-}
-- {-# INLINE icode7 #-}
-- {-# INLINE icode8 #-}
-- {-# INLINE icode9 #-}
-- {-# INLINE icode10 #-}
-- {-# INLINE icode11 #-}
-- {-# INLINE icode12 #-}
-- {-# INLINE icode13 #-}
-- {-# INLINE icode14 #-}

icode0 :: Int32 -> S Int32

icode1 :: EmbPrj a => Int32 -> a -> S Int32

icode2 :: (EmbPrj a, EmbPrj b) =>
          Int32 -> a -> b ->
          S Int32

icode3 :: (EmbPrj a, EmbPrj b, EmbPrj c) =>
          Int32 -> a -> b -> c ->
          S Int32

icode4 :: (EmbPrj a, EmbPrj b, EmbPrj c, EmbPrj d) =>
          Int32 -> a -> b -> c -> d ->
          S Int32

icode5 :: (EmbPrj a, EmbPrj b, EmbPrj c, EmbPrj d, EmbPrj e) =>
          Int32 -> a -> b -> c -> d -> e ->
          S Int32

icode6 :: (EmbPrj a, EmbPrj b, EmbPrj c, EmbPrj d, EmbPrj e, EmbPrj f) =>
          Int32 -> a -> b -> c -> d -> e -> f ->
          S Int32

icode7 :: ( EmbPrj a, EmbPrj b, EmbPrj c, EmbPrj d, EmbPrj e, EmbPrj f
          , EmbPrj g ) =>
          Int32 -> a -> b -> c -> d -> e -> f -> g ->
          S Int32

icode8 :: ( EmbPrj a, EmbPrj b, EmbPrj c, EmbPrj d, EmbPrj e, EmbPrj f
          , EmbPrj g, EmbPrj h ) =>
          Int32 -> a -> b -> c -> d -> e -> f -> g -> h ->
          S Int32

icode9 :: ( EmbPrj a, EmbPrj b, EmbPrj c, EmbPrj d, EmbPrj e, EmbPrj f
          , EmbPrj g, EmbPrj h, EmbPrj i ) =>
          Int32 -> a -> b -> c -> d -> e -> f -> g -> h -> i ->
          S Int32

icode10 :: ( EmbPrj a, EmbPrj b, EmbPrj c, EmbPrj d, EmbPrj e, EmbPrj f
           , EmbPrj g, EmbPrj h, EmbPrj i, EmbPrj j ) =>
           Int32 -> a -> b -> c -> d -> e -> f -> g -> h -> i -> j ->
           S Int32

icode11 :: ( EmbPrj a, EmbPrj b, EmbPrj c, EmbPrj d, EmbPrj e, EmbPrj f
           , EmbPrj g, EmbPrj h, EmbPrj i, EmbPrj j, EmbPrj k ) =>
           Int32 -> a -> b -> c -> d -> e -> f -> g -> h -> i -> j -> k ->
           S Int32

icode12 :: ( EmbPrj a, EmbPrj b, EmbPrj c, EmbPrj d, EmbPrj e, EmbPrj f
           , EmbPrj g, EmbPrj h, EmbPrj i, EmbPrj j, EmbPrj k, EmbPrj l ) =>
           Int32 -> a -> b -> c -> d -> e -> f -> g -> h -> i -> j -> k -> l ->
           S Int32

icode13 :: ( EmbPrj a, EmbPrj b, EmbPrj c, EmbPrj d, EmbPrj e, EmbPrj f
           , EmbPrj g, EmbPrj h, EmbPrj i, EmbPrj j, EmbPrj k, EmbPrj l
           , EmbPrj m ) =>
           Int32 -> a -> b -> c -> d -> e -> f -> g -> h -> i -> j -> k -> l -> m ->
           S Int32

icode14 :: ( EmbPrj a, EmbPrj b, EmbPrj c, EmbPrj d, EmbPrj e, EmbPrj f
           , EmbPrj g, EmbPrj h, EmbPrj i, EmbPrj j, EmbPrj k, EmbPrj l
           , EmbPrj m, EmbPrj n ) =>
           Int32 -> a -> b -> c -> d -> e -> f -> g -> h -> i -> j -> k -> l -> m -> n ->
           S Int32

icode0  tag                       = icodeN [tag]
icode1  tag a                     = icodeN . (tag :) =<< sequence [icode a]
icode2  tag a b                   = icodeN . (tag :) =<< sequence [icode a, icode b]
icode3  tag a b c                 = icodeN . (tag :) =<< sequence [icode a, icode b, icode c]
icode4  tag a b c d               = icodeN . (tag :) =<< sequence [icode a, icode b, icode c, icode d]
icode5  tag a b c d e             = icodeN . (tag :) =<< sequence [icode a, icode b, icode c, icode d, icode e]
icode6  tag a b c d e f           = icodeN . (tag :) =<< sequence [icode a, icode b, icode c, icode d, icode e, icode f]
icode7  tag a b c d e f g         = icodeN . (tag :) =<< sequence [icode a, icode b, icode c, icode d, icode e, icode f, icode g]
icode8  tag a b c d e f g h       = icodeN . (tag :) =<< sequence [icode a, icode b, icode c, icode d, icode e, icode f, icode g, icode h]
icode9  tag a b c d e f g h i     = icodeN . (tag :) =<< sequence [icode a, icode b, icode c, icode d, icode e, icode f, icode g, icode h, icode i]
icode10 tag a b c d e f g h i j   = icodeN . (tag :) =<< sequence [icode a, icode b, icode c, icode d, icode e, icode f, icode g, icode h, icode i, icode j]
icode11 tag a b c d e f g h i j k = icodeN . (tag :) =<< sequence [icode a, icode b, icode c, icode d, icode e, icode f, icode g, icode h, icode i, icode j, icode k]
icode12 tag a b c d e f g h i j k l = icodeN . (tag :) =<< sequence [icode a, icode b, icode c, icode d, icode e, icode f, icode g, icode h, icode i, icode j, icode k, icode l]
icode13 tag a b c d e f g h i j k l m = icodeN . (tag :) =<< sequence [icode a, icode b, icode c, icode d, icode e, icode f, icode g, icode h, icode i, icode j, icode k, icode l, icode m]
icode14 tag a b c d e f g h i j k l m n = icodeN . (tag :) =<< sequence [icode a, icode b, icode c, icode d, icode e, icode f, icode g, icode h, icode i, icode j, icode k, icode l, icode m, icode n]


-- Andreas, Makoto, AIM XX (2014-10-15):
-- No performance gain for INLINE here (neutral / slighly negative).
--
-- {-# INLINE icode0' #-}
-- {-# INLINE icode1' #-}
-- {-# INLINE icode2' #-}
-- {-# INLINE icode3' #-}
-- {-# INLINE icode4' #-}
-- {-# INLINE icode5' #-}
-- {-# INLINE icode6' #-}
-- {-# INLINE icode7' #-}
-- {-# INLINE icode8' #-}
-- {-# INLINE icode9' #-}
-- {-# INLINE icode10' #-}
-- {-# INLINE icode11' #-}
-- {-# INLINE icode12' #-}
-- {-# INLINE icode13' #-}
-- {-# INLINE icode14' #-}

icode0' :: S Int32

icode1' :: EmbPrj a => a -> S Int32

icode2' :: (EmbPrj a, EmbPrj b) =>
           a -> b ->
           S Int32

icode3' :: (EmbPrj a, EmbPrj b, EmbPrj c) =>
           a -> b -> c ->
           S Int32

icode4' :: (EmbPrj a, EmbPrj b, EmbPrj c, EmbPrj d) =>
           a -> b -> c -> d ->
           S Int32

icode5' :: (EmbPrj a, EmbPrj b, EmbPrj c, EmbPrj d, EmbPrj e) =>
           a -> b -> c -> d -> e ->
           S Int32

icode6' :: (EmbPrj a, EmbPrj b, EmbPrj c, EmbPrj d, EmbPrj e, EmbPrj f) =>
           a -> b -> c -> d -> e -> f ->
           S Int32

icode7' :: ( EmbPrj a, EmbPrj b, EmbPrj c, EmbPrj d, EmbPrj e, EmbPrj f
           , EmbPrj g ) =>
           a -> b -> c -> d -> e -> f -> g ->
           S Int32

icode8' :: ( EmbPrj a, EmbPrj b, EmbPrj c, EmbPrj d, EmbPrj e, EmbPrj f
           , EmbPrj g, EmbPrj h ) =>
           a -> b -> c -> d -> e -> f -> g -> h ->
           S Int32

icode9' :: ( EmbPrj a, EmbPrj b, EmbPrj c, EmbPrj d, EmbPrj e, EmbPrj f
           , EmbPrj g, EmbPrj h, EmbPrj i ) =>
           a -> b -> c -> d -> e -> f -> g -> h -> i ->
           S Int32

icode10' :: ( EmbPrj a, EmbPrj b, EmbPrj c, EmbPrj d, EmbPrj e, EmbPrj f
            , EmbPrj g, EmbPrj h, EmbPrj i, EmbPrj j ) =>
            a -> b -> c -> d -> e -> f -> g -> h -> i -> j ->
            S Int32

icode11' :: ( EmbPrj a, EmbPrj b, EmbPrj c, EmbPrj d, EmbPrj e, EmbPrj f
            , EmbPrj g, EmbPrj h, EmbPrj i, EmbPrj j, EmbPrj k ) =>
            a -> b -> c -> d -> e -> f -> g -> h -> i -> j -> k ->
            S Int32

icode12' :: ( EmbPrj a, EmbPrj b, EmbPrj c, EmbPrj d, EmbPrj e, EmbPrj f
            , EmbPrj g, EmbPrj h, EmbPrj i, EmbPrj j, EmbPrj k, EmbPrj l ) =>
            a -> b -> c -> d -> e -> f -> g -> h -> i -> j -> k -> l ->
            S Int32

icode13' :: ( EmbPrj a, EmbPrj b, EmbPrj c, EmbPrj d, EmbPrj e, EmbPrj f
            , EmbPrj g, EmbPrj h, EmbPrj i, EmbPrj j, EmbPrj k, EmbPrj l
            , EmbPrj m ) =>
            a -> b -> c -> d -> e -> f -> g -> h -> i -> j -> k -> l -> m ->
            S Int32

icode14' :: ( EmbPrj a, EmbPrj b, EmbPrj c, EmbPrj d, EmbPrj e, EmbPrj f
            , EmbPrj g, EmbPrj h, EmbPrj i, EmbPrj j, EmbPrj k, EmbPrj l
            , EmbPrj m, EmbPrj n ) =>
            a -> b -> c -> d -> e -> f -> g -> h -> i -> j -> k -> l -> m -> n ->
            S Int32

icode0'                        = icodeN []
icode1'  a                     = icodeN =<< sequence [icode a]
icode2'  a b                   = icodeN =<< sequence [icode a, icode b]
icode3'  a b c                 = icodeN =<< sequence [icode a, icode b, icode c]
icode4'  a b c d               = icodeN =<< sequence [icode a, icode b, icode c, icode d]
icode5'  a b c d e             = icodeN =<< sequence [icode a, icode b, icode c, icode d, icode e]
icode6'  a b c d e f           = icodeN =<< sequence [icode a, icode b, icode c, icode d, icode e, icode f]
icode7'  a b c d e f g         = icodeN =<< sequence [icode a, icode b, icode c, icode d, icode e, icode f, icode g]
icode8'  a b c d e f g h       = icodeN =<< sequence [icode a, icode b, icode c, icode d, icode e, icode f, icode g, icode h]
icode9'  a b c d e f g h i     = icodeN =<< sequence [icode a, icode b, icode c, icode d, icode e, icode f, icode g, icode h, icode i]
icode10' a b c d e f g h i j   = icodeN =<< sequence [icode a, icode b, icode c, icode d, icode e, icode f, icode g, icode h, icode i, icode j]
icode11' a b c d e f g h i j k = icodeN =<< sequence [icode a, icode b, icode c, icode d, icode e, icode f, icode g, icode h, icode i, icode j, icode k]
icode12' a b c d e f g h i j k l = icodeN =<< sequence [icode a, icode b, icode c, icode d, icode e, icode f, icode g, icode h, icode i, icode j, icode k, icode l]
icode13' a b c d e f g h i j k l m = icodeN =<< sequence [icode a, icode b, icode c, icode d, icode e, icode f, icode g, icode h, icode i, icode j, icode k, icode l, icode m]
icode14' a b c d e f g h i j k l m n = icodeN =<< sequence [icode a, icode b, icode c, icode d, icode e, icode f, icode g, icode h, icode i, icode j, icode k, icode l, icode m, icode n]

valu0 :: a -> R a

valu1 :: EmbPrj a => (a -> b) -> Int32 -> R b

valu2 :: (EmbPrj a, EmbPrj b) =>
         (a -> b -> c) ->
         Int32 -> Int32 ->
         R c

valu3 :: (EmbPrj a, EmbPrj b, EmbPrj c) =>
         (a -> b -> c -> d) ->
         Int32 -> Int32 -> Int32 ->
         R d

valu4 :: (EmbPrj a, EmbPrj b, EmbPrj c, EmbPrj d) =>
         (a -> b -> c -> d -> e) ->
         Int32 -> Int32 -> Int32 -> Int32 ->
         R e

valu5 :: (EmbPrj a, EmbPrj b, EmbPrj c, EmbPrj d, EmbPrj e) =>
         (a -> b -> c -> d -> e -> f) ->
         Int32 -> Int32 -> Int32 -> Int32 -> Int32 ->
         R f

valu6 :: (EmbPrj a, EmbPrj b, EmbPrj c, EmbPrj d, EmbPrj e, EmbPrj f) =>
         (a -> b -> c -> d -> e -> f -> g) ->
         Int32 -> Int32 -> Int32 -> Int32 -> Int32 -> Int32 ->
         R g

valu7 :: ( EmbPrj a, EmbPrj b, EmbPrj c, EmbPrj d, EmbPrj e, EmbPrj f
         , EmbPrj g ) =>
         (a -> b -> c -> d -> e -> f -> g -> h) ->
         Int32 -> Int32 -> Int32 -> Int32 -> Int32 -> Int32 -> Int32 ->
         R h

valu8 :: ( EmbPrj a, EmbPrj b, EmbPrj c, EmbPrj d, EmbPrj e, EmbPrj f
         , EmbPrj g, EmbPrj h ) =>
         (a -> b -> c -> d -> e -> f -> g -> h -> i) ->
         Int32 -> Int32 -> Int32 -> Int32 -> Int32 -> Int32 -> Int32 -> Int32 ->
         R i

valu9 :: ( EmbPrj a, EmbPrj b, EmbPrj c, EmbPrj d, EmbPrj e, EmbPrj f
         , EmbPrj g, EmbPrj h, EmbPrj i ) =>
         (a -> b -> c -> d -> e -> f -> g -> h -> i -> j) ->
         Int32 -> Int32 -> Int32 -> Int32 -> Int32 -> Int32 -> Int32 -> Int32 -> Int32 ->
         R j

valu10 :: ( EmbPrj a, EmbPrj b, EmbPrj c, EmbPrj d, EmbPrj e, EmbPrj f
          , EmbPrj g, EmbPrj h, EmbPrj i, EmbPrj j ) =>
          (a -> b -> c -> d -> e -> f -> g -> h -> i -> j -> k) ->
          Int32 -> Int32 -> Int32 -> Int32 -> Int32 -> Int32 -> Int32 -> Int32 -> Int32 -> Int32 ->
          R k

valu11 :: ( EmbPrj a, EmbPrj b, EmbPrj c, EmbPrj d, EmbPrj e, EmbPrj f
          , EmbPrj g, EmbPrj h, EmbPrj i, EmbPrj j, EmbPrj k ) =>
          (a -> b -> c -> d -> e -> f -> g -> h -> i -> j -> k -> l) ->
          Int32 -> Int32 -> Int32 -> Int32 -> Int32 -> Int32 -> Int32 -> Int32 -> Int32 -> Int32 -> Int32 ->
         R l

valu12 :: ( EmbPrj a, EmbPrj b, EmbPrj c, EmbPrj d, EmbPrj e, EmbPrj f
          , EmbPrj g, EmbPrj h, EmbPrj i, EmbPrj j, EmbPrj k, EmbPrj l ) =>
          (a -> b -> c -> d -> e -> f -> g -> h -> i -> j -> k -> l -> m) ->
          Int32 -> Int32 -> Int32 -> Int32 -> Int32 -> Int32 -> Int32 -> Int32 -> Int32 -> Int32 -> Int32 -> Int32 ->
          R m

valu13 :: ( EmbPrj a, EmbPrj b, EmbPrj c, EmbPrj d, EmbPrj e, EmbPrj f
          , EmbPrj g, EmbPrj h, EmbPrj i, EmbPrj j, EmbPrj k, EmbPrj l
          , EmbPrj m ) =>
          (a -> b -> c -> d -> e -> f -> g -> h -> i -> j -> k -> l -> m -> n) ->
          Int32 -> Int32 -> Int32 -> Int32 -> Int32 -> Int32 -> Int32 -> Int32 -> Int32 -> Int32 -> Int32 -> Int32 -> Int32 ->
          R n

valu14 :: ( EmbPrj a, EmbPrj b, EmbPrj c, EmbPrj d, EmbPrj e, EmbPrj f
          , EmbPrj g, EmbPrj h, EmbPrj i, EmbPrj j, EmbPrj k, EmbPrj l
          , EmbPrj m, EmbPrj n ) =>
          (a -> b -> c -> d -> e -> f -> g -> h -> i -> j -> k -> l -> m -> n -> o) ->
          Int32 -> Int32 -> Int32 -> Int32 -> Int32 -> Int32 -> Int32 -> Int32 -> Int32 -> Int32 -> Int32 -> Int32 -> Int32 -> Int32 ->
          R o

valu0  z                           = return z
valu1  z a                         = valu0 z                        `ap` value a
valu2  z a b                       = valu1 z a                      `ap` value b
valu3  z a b c                     = valu2 z a b                    `ap` value c
valu4  z a b c d                   = valu3 z a b c                  `ap` value d
valu5  z a b c d e                 = valu4 z a b c d                `ap` value e
valu6  z a b c d e f               = valu5 z a b c d e              `ap` value f
valu7  z a b c d e f g             = valu6 z a b c d e f            `ap` value g
valu8  z a b c d e f g h           = valu7 z a b c d e f g          `ap` value h
valu9  z a b c d e f g h i         = valu8 z a b c d e f g h        `ap` value i
valu10 z a b c d e f g h i j       = valu9 z a b c d e f g h i      `ap` value j
valu11 z a b c d e f g h i j k     = valu10 z a b c d e f g h i j   `ap` value k
valu12 z a b c d e f g h i j k l   = valu11 z a b c d e f g h i j k `ap` value l
valu13 z a b c d e f g h i j k l m = valu12 z a b c d e f g h i j k l `ap` value m
valu14 z a b c d e f g h i j k l m n = valu13 z a b c d e f g h i j k l m `ap` value n
