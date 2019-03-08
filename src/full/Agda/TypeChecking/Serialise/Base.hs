{-# LANGUAGE CPP                  #-}
{-# LANGUAGE DataKinds            #-}
{-# LANGUAGE TypeFamilies         #-}
{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE UndecidableInstances #-}

module Agda.TypeChecking.Serialise.Base where

import Control.Exception (evaluate)
import Control.Monad
import Control.Monad.Catch (catchAll)
import Control.Monad.Reader
import Control.Monad.State.Strict (StateT, gets)

import Data.Proxy

import Data.Array.IArray
import qualified Data.ByteString.Lazy as L
import Data.Hashable
import qualified Data.HashTable.IO as H
import Data.Int (Int32)
import Data.Maybe
import qualified Data.Binary as B
import qualified Data.Binary.Get as B
import Data.Text.Lazy (Text)
import Data.Typeable ( cast, Typeable, typeOf, TypeRep )

import Agda.Syntax.Common (NameId)
import Agda.Syntax.Internal (Term, QName(..), ModuleName(..), nameId)
import Agda.TypeChecking.Monad.Base (TypeError(GenericError), ModuleToSource)

import Agda.Utils.FileName
import Agda.Utils.IORef
import Agda.Utils.Lens
import Agda.Utils.Monad
import Agda.Utils.Pointer
import Agda.Utils.Except (ExceptT, throwError)
import Agda.Utils.TypeLevel

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
  , textD        :: !(HashTable Text    Int32)    -- ^ Written to interface file.
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
  , textC        :: !(IORef FreshAndReuse)
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
  , textE     :: !(Array Int32 Text)     -- ^ Obtained from interface file.
  , integerE  :: !(Array Int32 Integer)  -- ^ Obtained from interface file.
  , doubleE   :: !(Array Int32 Double)   -- ^ Obtained from interface file.
  , nodeMemo  :: !Memo
    -- ^ Created and modified by decoder.
    --   Used to introduce sharing while deserializing objects.
  , modFile   :: !ModuleToSource
    -- ^ Maps module names to file names. Constructed by the decoder.
  , includes  :: [AbsolutePath]
    -- ^ The include directories.
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

  -- Simple enumeration types can be (de)serialized using (from/to)Enum.

  default value :: (Enum a) => Int32 -> R a
  value i = liftIO (evaluate (toEnum (fromIntegral i))) `catchAll` const malformed

  default icod_ :: (Enum a) => a -> S Int32
  icod_ = return . fromIntegral . fromEnum

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

icodeNode :: Node -> S Int32
icodeNode key = do
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

-- | @icodeArgs proxy (a1, ..., an)@ maps @icode@ over @a1@, ..., @an@
--   and returns the corresponding list of @Int32@.

class ICODE t b where
  icodeArgs :: IsBase t ~ b => All EmbPrj (Domains t) =>
               Proxy t -> Products (Domains t) -> S [Int32]

instance IsBase t ~ 'True => ICODE t 'True where
  icodeArgs _ _  = return []

instance ICODE t (IsBase t) => ICODE (a -> t) 'False where
  icodeArgs _ (a , as) = icode a >>= \ hd -> (hd :) <$> icodeArgs (Proxy :: Proxy t) as

-- | @icodeN tag t a1 ... an@ serialises the arguments @a1@, ..., @an@ of the
--   constructor @t@ together with a tag @tag@ picked to disambiguate between
--   different constructors.
--   It corresponds to @icodeNode . (tag :) =<< mapM icode [a1, ..., an]@

{-# INLINE icodeN #-}
icodeN :: forall t. ICODE t (IsBase t) => Currying (Domains t) (S Int32) =>
          All EmbPrj (Domains t) =>
          Int32 -> t -> Arrows (Domains t) (S Int32)
icodeN tag _ =
  currys (Proxy :: Proxy (Domains t)) (Proxy :: Proxy (S Int32)) $ \ args ->
  icodeNode . (tag :) =<< icodeArgs (Proxy :: Proxy t) args

-- | @icodeN'@ is the same as @icodeN@ except that there is no tag
{-# INLINE icodeN' #-}
icodeN' :: forall t. ICODE t (IsBase t) => Currying (Domains t) (S Int32) =>
           All EmbPrj (Domains t) =>
           t -> Arrows (Domains t) (S Int32)
icodeN' _ =
  currys (Proxy :: Proxy (Domains t)) (Proxy :: Proxy (S Int32)) $ \ args ->
  icodeNode =<< icodeArgs (Proxy :: Proxy t) args

-- Instead of having up to 25 versions of @valu N@, we define
-- the class VALU which generates them by typeclass resolution.
-- All of these should get inlined at compile time.

class VALU t b where

  valuN' :: b ~ IsBase t =>
            All EmbPrj (Domains t) =>
            t -> Products (Constant Int32 (Domains t)) -> R (CoDomain t)

  valueArgs :: b ~ IsBase t =>
               All EmbPrj (CoDomain t ': Domains t) =>
               Proxy t -> Node -> Maybe (Products (Constant Int32 (Domains t)))

instance VALU t 'True where

  valuN' c () = return c

  valueArgs _ xs = case xs of
    [] -> Just ()
    _  -> Nothing


instance VALU t (IsBase t) => VALU (a -> t) 'False where

  valuN' c (a, as) = value a >>= \ v -> valuN' (c v) as

  valueArgs _ xs = case xs of
    (x : xs') -> (x,) <$> valueArgs (Proxy :: Proxy t) xs'
    _         -> Nothing

{-# INLINE valuN #-}
valuN :: forall t. VALU t (IsBase t) =>
         Currying (Constant Int32 (Domains t)) (R (CoDomain t)) =>
         All EmbPrj (Domains t) =>
         t -> Arrows (Constant Int32 (Domains t)) (R (CoDomain t))
valuN f = currys (Proxy :: Proxy (Constant Int32 (Domains t)))
                 (Proxy :: Proxy (R (CoDomain t)))
                 (valuN' f)

{-# INLINE valueN #-}
valueN :: forall t. VALU t (IsBase t) =>
          All EmbPrj (CoDomain t ': Domains t) =>
          t -> Int32 -> R (CoDomain t)
valueN t = vcase valu where
  valu int32s = case valueArgs (Proxy :: Proxy t) int32s of
                  Nothing -> malformed
                  Just vs -> valuN' t vs
