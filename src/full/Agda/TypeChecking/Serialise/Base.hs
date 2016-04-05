{-# LANGUAGE CPP                       #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE ScopedTypeVariables       #-}

module Agda.TypeChecking.Serialise.Base where

import Control.Applicative
import Control.Monad
import Control.Monad.Reader
import Control.Monad.State.Strict (StateT, gets)

import Data.Array.IArray
import qualified Data.ByteString.Lazy as L
import Data.Hashable
import qualified Data.HashTable.IO as H
import Data.Int (Int32)
import Data.Maybe
import qualified Data.Binary as B
import qualified Data.Binary.Get as B
import Data.Typeable ( cast, Typeable, typeOf, TypeRep )

import Agda.Packaging.Base
import Agda.Syntax.Common (NameId)
import Agda.Syntax.Internal (Term, QName(..), ModuleName(..), nameId)
import Agda.TypeChecking.Monad.Base (TypeError(GenericError), ModuleToSource)

import Agda.Utils.FileName
import Agda.Utils.IORef
import Agda.Utils.Lens
import Agda.Utils.Monad
import Agda.Utils.Pointer
import Agda.Utils.Except (ExceptT, throwError)

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

-- | Two 'QName's are equal if their @QNameId@ is equal.
type QNameId = [NameId]

-- | Computing a qualified names composed ID.
qnameId :: QName -> QNameId
qnameId (QName (MName ns) n) = map nameId $ n:ns

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
data U = forall a . Typeable a => U !a

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
  , packageDBStack :: PkgDBStack
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
  :: (Ord a, Hashable a)
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

icode15 :: ( EmbPrj a, EmbPrj b, EmbPrj c, EmbPrj d, EmbPrj e, EmbPrj f
           , EmbPrj g, EmbPrj h, EmbPrj i, EmbPrj j, EmbPrj k, EmbPrj l
           , EmbPrj m, EmbPrj n, EmbPrj o ) =>
           Int32 -> a -> b -> c -> d -> e -> f -> g -> h -> i -> j -> k -> l -> m -> n -> o ->
           S Int32

icode0 tag = icodeN [tag]
icode1 tag a = icodeN . (tag :) =<< sequence [icode a]
icode2 tag a b = icodeN . (tag :) =<< sequence [icode a, icode b]
icode3 tag a b c = icodeN . (tag :) =<< sequence [icode a, icode b, icode c]
icode4 tag a b c d = icodeN . (tag :) =<< sequence [icode a, icode b, icode c, icode d]
icode5 tag a b c d e = icodeN . (tag :) =<< sequence [icode a, icode b, icode c, icode d, icode e]
icode6 tag a b c d e f = icodeN . (tag :) =<< sequence [icode a, icode b, icode c, icode d, icode e, icode f]
icode7 tag a b c d e f g = icodeN . (tag :) =<< sequence [icode a, icode b, icode c, icode d, icode e, icode f, icode g]
icode8 tag a b c d e f g h = icodeN . (tag :) =<< sequence [icode a, icode b, icode c, icode d, icode e, icode f, icode g, icode h]
icode9 tag a b c d e f g h i = icodeN . (tag :) =<< sequence [icode a, icode b, icode c, icode d, icode e, icode f, icode g, icode h, icode i]
icode10 tag a b c d e f g h i j = icodeN . (tag :) =<< sequence [icode a, icode b, icode c, icode d, icode e, icode f, icode g, icode h, icode i, icode j]
icode11 tag a b c d e f g h i j k = icodeN . (tag :) =<< sequence [icode a, icode b, icode c, icode d, icode e, icode f, icode g, icode h, icode i, icode j, icode k]
icode12 tag a b c d e f g h i j k l = icodeN . (tag :) =<< sequence [icode a, icode b, icode c, icode d, icode e, icode f, icode g, icode h, icode i, icode j, icode k, icode l]
icode13 tag a b c d e f g h i j k l m = icodeN . (tag :) =<< sequence [icode a, icode b, icode c, icode d, icode e, icode f, icode g, icode h, icode i, icode j, icode k, icode l, icode m]
icode14 tag a b c d e f g h i j k l m n = icodeN . (tag :) =<< sequence [icode a, icode b, icode c, icode d, icode e, icode f, icode g, icode h, icode i, icode j, icode k, icode l, icode m, icode n]
icode15 tag a b c d e f g h i j k l m n o = icodeN . (tag :) =<< sequence [icode a, icode b, icode c, icode d, icode e, icode f, icode g, icode h, icode i, icode j, icode k, icode l, icode m, icode n, icode o]


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

icode0' = icodeN []
icode1' a = icodeN =<< sequence [icode a]
icode2' a b = icodeN =<< sequence [icode a, icode b]
icode3' a b c = icodeN =<< sequence [icode a, icode b, icode c]
icode4' a b c d = icodeN =<< sequence [icode a, icode b, icode c, icode d]
icode5' a b c d e = icodeN =<< sequence [icode a, icode b, icode c, icode d, icode e]
icode6' a b c d e f = icodeN =<< sequence [icode a, icode b, icode c, icode d, icode e, icode f]
icode7' a b c d e f g = icodeN =<< sequence [icode a, icode b, icode c, icode d, icode e, icode f, icode g]
icode8' a b c d e f g h = icodeN =<< sequence [icode a, icode b, icode c, icode d, icode e, icode f, icode g, icode h]
icode9' a b c d e f g h i = icodeN =<< sequence [icode a, icode b, icode c, icode d, icode e, icode f, icode g, icode h, icode i]
icode10' a b c d e f g h i j = icodeN =<< sequence [icode a, icode b, icode c, icode d, icode e, icode f, icode g, icode h, icode i, icode j]
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


valu15 :: ( EmbPrj a, EmbPrj b, EmbPrj c, EmbPrj d, EmbPrj e, EmbPrj f
          , EmbPrj g, EmbPrj h, EmbPrj i, EmbPrj j, EmbPrj k, EmbPrj l
          , EmbPrj m, EmbPrj n, EmbPrj o ) =>
          (a -> b -> c -> d -> e -> f -> g -> h -> i -> j -> k -> l -> m -> n -> o -> p) ->
          Int32 -> Int32 -> Int32 -> Int32 -> Int32 -> Int32 -> Int32 -> Int32 -> Int32 -> Int32 -> Int32 -> Int32 -> Int32 -> Int32 -> Int32 ->
          R p

valu0 z = return z
valu1 z a = valu0 z `ap` value a
valu2 z a b = valu1 z a `ap` value b
valu3 z a b c = valu2 z a b `ap` value c
valu4 z a b c d = valu3 z a b c `ap` value d
valu5 z a b c d e = valu4 z a b c d `ap` value e
valu6 z a b c d e f = valu5 z a b c d e `ap` value f
valu7 z a b c d e f g = valu6 z a b c d e f `ap` value g
valu8 z a b c d e f g h = valu7 z a b c d e f g `ap` value h
valu9 z a b c d e f g h i = valu8 z a b c d e f g h `ap` value i
valu10 z a b c d e f g h i j = valu9 z a b c d e f g h i `ap` value j
valu11 z a b c d e f g h i j k = valu10 z a b c d e f g h i j `ap` value k
valu12 z a b c d e f g h i j k l = valu11 z a b c d e f g h i j k `ap` value l
valu13 z a b c d e f g h i j k l m = valu12 z a b c d e f g h i j k l `ap` value m
valu14 z a b c d e f g h i j k l m n = valu13 z a b c d e f g h i j k l m `ap` value n
valu15 z a b c d e f g h i j k l m n o = valu14 z a b c d e f g h i j k l m n `ap` value o
