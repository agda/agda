{-# LANGUAGE CPP                  #-}
{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE DataKinds            #-}
{-# LANGUAGE UndecidableInstances #-} -- Due to ICODE vararg typeclass
{-# LANGUAGE MagicHash            #-}
{-# LANGUAGE UnboxedTuples        #-}

{-
András, 2023-10-2:

All code in Agda/TypeChecking/Serialise should be strict, since serialization necessarily
forces all data, eventually.
  - (<$!>) should be used instead of lazy fmap.
  - Any redex that's passed to `return`, a lazy constructor, or a function, should
    be forced beforehand with strict `let`, strict binding or ($!).
-}

module Agda.TypeChecking.Serialise.Base where

import qualified Control.Exception as E
import Control.Monad ((<$!>))
import Control.Monad.Except
import Control.Monad.IO.Class     ( MonadIO(..) )
import Control.Monad.Reader
import Control.Monad.State.Strict (StateT, gets)

import Data.Proxy

import Data.Array.IArray
import Data.Array.IO
import qualified Data.HashMap.Strict as Hm
import qualified Data.ByteString.Lazy as L
import Data.Hashable
import Data.Int (Int32)
import Data.Maybe
import qualified Data.Binary as B
import qualified Data.Binary.Get as B
import qualified Data.Text      as T
import qualified Data.Text.Lazy as TL
import Data.Typeable ( cast, Typeable, TypeRep, typeRep, typeRepFingerprint )
import GHC.Exts (Word(..), timesWord2#, xor#, Any)
import GHC.Fingerprint.Type
import Unsafe.Coerce

import Agda.Syntax.Common (NameId)
import Agda.Syntax.Internal (Term, QName(..), ModuleName(..), nameId)
import Agda.TypeChecking.Monad.Base (TypeError(GenericError), ModuleToSource)

import Agda.Utils.FileName
import Agda.Utils.HashTable (HashTable)
import qualified Agda.Utils.HashTable as H
import Agda.Utils.IORef
import Agda.Utils.Lens
import Agda.Utils.Monad
import Agda.Utils.Pointer
import Agda.Utils.TypeLevel

-- | Constructor tag (maybe omitted) and argument indices.
data Node = Empty | Cons !Int32 !Node deriving Eq

instance Hashable Node where
  -- Adapted from https://github.com/tkaitchuck/aHash/wiki/AHash-fallback-algorithm
  hashWithSalt h n = fromIntegral (go (fromIntegral h) n) where
    xor (W# x) (W# y) = W# (xor# x y)

    foldedMul :: Word -> Word -> Word
    foldedMul (W# x) (W# y) = case timesWord2# x y of (# hi, lo #) -> W# (xor# hi lo)

    combine :: Word -> Word -> Word
    combine x y = foldedMul (xor x y) 11400714819323198549

    go :: Word -> Node -> Word
    go !h Empty       = h
    go  h (Cons n ns) = go (combine h (fromIntegral n)) ns

  hash = hashWithSalt 3032525626373534813

instance B.Binary Node where

  get = go =<< B.get where

    go :: Int -> B.Get Node
    go n | n <= 0 =
      pure Empty
    go n = do
      !x    <- B.get
      !node <- go (n - 1)
      pure $ Cons x node

  put n = B.put (len n) <> go n where

    len :: Node -> Int
    len = go 0 where
      go !acc Empty     = acc
      go acc (Cons _ n) = go (acc + 1) n

    go :: Node -> B.Put
    go Empty       = mempty
    go (Cons n ns) = B.put n <> go ns

-- | Association lists mapping TypeRep fingerprints to values. In some cases
--   values with different types have the same serialized representation. This
--   structure disambiguates them.
data MemoEntry = MEEmpty | MECons {-# unpack #-} !Fingerprint !Any !MemoEntry

-- 2023-10-2 András: `typeRepFingerprint` usually inlines a 4-way case, which
-- yields significant code size increase as GHC often inlines the same code into
-- the branches. This wouldn't matter in "normal" code but the serialization
-- instances use very heavy inlining. The NOINLINE cuts down on the code size.
fingerprintNoinline :: TypeRep -> Fingerprint
fingerprintNoinline rep = typeRepFingerprint rep
{-# NOINLINE fingerprintNoinline #-}

lookupME :: forall a b. Proxy a -> Fingerprint -> MemoEntry -> (a -> b) -> b -> b
lookupME proxy fprint me found notfound = go fprint me where
  go :: Fingerprint -> MemoEntry -> b
  go fp MEEmpty =
    notfound
  go fp (MECons fp' x me)
    | fp == fp' = found (unsafeCoerce x)
    | True      = go fp me
{-# NOINLINE lookupME #-}

-- | Structure providing fresh identifiers for hash map
--   and counting hash map hits (i.e. when no fresh identifier required).
#ifdef DEBUG
data FreshAndReuse = FreshAndReuse
  { farFresh :: !Int32 -- ^ Number of hash map misses.
  , farReuse :: !Int32 -- ^ Number of hash map hits.
  }
#else
newtype FreshAndReuse = FreshAndReuse
  { farFresh :: Int32 -- ^ Number of hash map misses.
  }
#endif

farEmpty :: FreshAndReuse
farEmpty = FreshAndReuse 0
#ifdef DEBUG
                           0
#endif

lensFresh :: Lens' FreshAndReuse Int32
lensFresh f r = f (farFresh r) <&> \ i -> r { farFresh = i }
{-# INLINE lensFresh #-}

#ifdef DEBUG
lensReuse :: Lens' FreshAndReuse Int32
lensReuse f r = f (farReuse r) <&> \ i -> r { farReuse = i }
{-# INLINE lensReuse #-}
#endif

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
  , lTextD       :: !(HashTable TL.Text Int32)    -- ^ Written to interface file.
  , sTextD       :: !(HashTable T.Text  Int32)    -- ^ Written to interface file.
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
  , lTextC       :: !(IORef FreshAndReuse)
  , sTextC       :: !(IORef FreshAndReuse)
  , integerC     :: !(IORef FreshAndReuse)
  , doubleC      :: !(IORef FreshAndReuse)
  , termC        :: !(IORef FreshAndReuse)
  , nameC        :: !(IORef FreshAndReuse)
  , qnameC       :: !(IORef FreshAndReuse)
  , stats        :: !(HashTable String Int)
  , collectStats :: !Bool
    -- ^ If @True@ collect in @stats@ the quantities of
    --   calls to @icode@ for each @Typeable a@.
  }

-- | Creates an empty dictionary.
emptyDict
  :: Bool
     -- ^ Collect statistics for @icode@ calls?
  -> IO Dict
emptyDict collectStats = Dict
  <$> H.empty
  <*> H.empty
  <*> H.empty
  <*> H.empty
  <*> H.empty
  <*> H.empty
  <*> H.empty
  <*> H.empty
  <*> H.empty
  <*> newIORef farEmpty
  <*> newIORef farEmpty
  <*> newIORef farEmpty
  <*> newIORef farEmpty
  <*> newIORef farEmpty
  <*> newIORef farEmpty
  <*> newIORef farEmpty
  <*> newIORef farEmpty
  <*> newIORef farEmpty
  <*> H.empty
  <*> pure collectStats

-- | Univeral memo structure, to introduce sharing during decoding
type Memo = IOArray Int32 MemoEntry

-- | State of the decoder.
data St = St
  { nodeE     :: !(Array Int32 [Int32])  -- ^ Obtained from interface file.
  , stringE   :: !(Array Int32 String)   -- ^ Obtained from interface file.
  , lTextE    :: !(Array Int32 TL.Text)  -- ^ Obtained from interface file.
  , sTextE    :: !(Array Int32 T.Text)   -- ^ Obtained from interface file.
  , integerE  :: !(Array Int32 Integer)  -- ^ Obtained from interface file.
  , doubleE   :: !(Array Int32 Double)   -- ^ Obtained from interface file.
  , nodeMemo  :: !Memo
    -- ^ Created and modified by decoder.
    --   Used to introduce sharing while deserializing objects.
  , modFile   :: !ModuleToSource
    -- ^ Maps module names to file names. Constructed by the decoder.
  , includes  :: ![AbsolutePath]
    -- ^ The include directories.
  }

-- | Monad used by the encoder.

type S a = ReaderT Dict IO a

-- | Monad used by the decoder.
--
-- 'TCM' is not used because the associated overheads would make
-- decoding slower.

type R = StateT St IO

-- | Throws an error which is suitable when the data stream is
-- malformed.

malformed :: R a
malformed = liftIO $ E.throwIO $ E.ErrorCall "Malformed input."
{-# NOINLINE malformed #-} -- 2023-10-2 András: cold code, so should be out-of-line.

class Typeable a => EmbPrj a where
  icode :: a -> S Int32  -- ^ Serialization (wrapper).
  icod_ :: a -> S Int32  -- ^ Serialization (worker).
  value :: Int32 -> R a  -- ^ Deserialization.

  icode a = do
    !r <- icod_ a
    tickICode a
    pure r
  {-# INLINE icode #-}

  -- Simple enumeration types can be (de)serialized using (from/to)Enum.
  default value :: (Enum a, Bounded a) => Int32 -> R a
  value i =
    let i' = fromIntegral i in
    if i' >= fromEnum (minBound :: a) && i' <= fromEnum (maxBound :: a)
    then pure $! toEnum i'
    else malformed

  default icod_ :: (Enum a, Bounded a) => a -> S Int32
  icod_ x = return $! fromIntegral $! fromEnum x

-- | The actual logic of `tickICode` is cold code, so it's out-of-line,
--   to decrease code size and avoid cache pollution.
goTickIcode :: forall a. Typeable a => Proxy a -> S ()
goTickIcode p = do
  let key = "icode " ++ show (typeRep p)
  hmap <- asks stats
  liftIO $ do
    n <- fromMaybe 0 <$> H.lookup hmap key
    H.insert hmap key $! n + 1
{-# NOINLINE goTickIcode #-}

-- | Increase entry for @a@ in 'stats'.
tickICode :: forall a. Typeable a => a -> S ()
tickICode _ = whenM (asks collectStats) $ goTickIcode (Proxy :: Proxy a)
{-# INLINE tickICode #-}

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
#ifdef DEBUG
        modifyIORef' c $ over lensReuse (+1)
#endif
        return $! i
      Nothing -> do
        !fresh <- (^.lensFresh) <$> do readModifyIORef' c $ over lensFresh (+1)
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
#ifdef DEBUG
        modifyIORef' c $ over lensReuse (+1)
#endif
        return $! i
      Nothing -> do
        !fresh <- (^.lensFresh) <$> do readModifyIORef' c $ over lensFresh (+1)
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
#ifdef DEBUG
        modifyIORef' c $ over lensReuse (+1)
#endif
        return $! i
      Nothing -> do
        !fresh <- (^.lensFresh) <$> do readModifyIORef' c $ over lensFresh (+1)
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
#ifdef DEBUG
        modifyIORef' c $ over lensReuse (+1)
#endif
        return i
      Nothing -> do
        !fresh <- (^.lensFresh) <$> do readModifyIORef' c $ over lensFresh (+1)
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
#ifdef DEBUG
        modifyIORef' c $ over lensReuse (+1)
#endif
        return $! i
      Nothing -> do
        !fresh <- (^.lensFresh) <$> do readModifyIORef' c $ over lensFresh (+1)
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
#ifdef DEBUG
        modifyIORef' st $ over lensReuse (+ 1)
#endif
        return $! i
      Nothing -> do
        liftIO $ modifyIORef' st $ over lensFresh (+1)
        !i <- icodeP
        liftIO $ H.insert h a i
        return i

{-# INLINE vcase #-}
-- | @vcase value ix@ decodes thing represented by @ix :: Int32@
--   via the @valu@ function and stores it in 'nodeMemo'.
--   If @ix@ is present in 'nodeMemo', @valu@ is not used, but
--   the thing is read from 'nodeMemo' instead.
vcase :: forall a . EmbPrj a => ([Int32] -> R a) -> Int32 -> R a
vcase valu = \ix -> do
    memo <- gets nodeMemo
    let fp = fingerprintNoinline (typeRep (Proxy :: Proxy a))
    -- to introduce sharing, see if we have seen a thing
    -- represented by ix before
    slot <- liftIO $ readArray memo ix
    lookupME (Proxy :: Proxy a) fp slot
      -- use the stored value
      pure
      -- read new value and save it
      do !v <- valu . (! ix) =<< gets nodeE
         liftIO $ writeArray memo ix $! MECons fp (unsafeCoerce v) slot
         return v

-- | @icodeArgs proxy (a1, ..., an)@ maps @icode@ over @a1@, ..., @an@
--   and returns the corresponding list of @Int32@.

class ICODE t b where
  icodeArgs :: IsBase t ~ b => All EmbPrj (Domains t) =>
               Proxy t -> StrictProducts (Domains t) -> S Node

instance IsBase t ~ 'True => ICODE t 'True where
  icodeArgs _ _  = return Empty
  {-# INLINE icodeArgs #-}

instance ICODE t (IsBase t) => ICODE (a -> t) 'False where
  icodeArgs _ (Pair a as) = do
    !hd   <- icode a
    !node <- icodeArgs (Proxy :: Proxy t) as
    pure $ Cons hd node
  {-# INLINE icodeArgs #-}

-- | @icodeN tag t a1 ... an@ serialises the arguments @a1@, ..., @an@ of the
--   constructor @t@ together with a tag @tag@ picked to disambiguate between
--   different constructors.
--   It corresponds to @icodeNode . (tag :) =<< mapM icode [a1, ..., an]@

{-# INLINE icodeN #-}
icodeN :: forall t. ICODE t (IsBase t) => StrictCurrying (Domains t) (S Int32) =>
          All EmbPrj (Domains t) =>
          Int32 -> t -> Arrows (Domains t) (S Int32)
icodeN tag _ =
  strictCurrys (Proxy :: Proxy (Domains t)) (Proxy :: Proxy (S Int32)) $ \ !args -> do
    !node <- icodeArgs (Proxy :: Proxy t) args
    icodeNode $ Cons tag node

-- | @icodeN'@ is the same as @icodeN@ except that there is no tag
{-# INLINE icodeN' #-}
icodeN' :: forall t. ICODE t (IsBase t) => StrictCurrying (Domains t) (S Int32) =>
           All EmbPrj (Domains t) =>
           t -> Arrows (Domains t) (S Int32)
icodeN' _ =
  strictCurrys (Proxy :: Proxy (Domains t)) (Proxy :: Proxy (S Int32)) $ \ !args -> do
    !node <- icodeArgs (Proxy :: Proxy t) args
    icodeNode node

-- Instead of having up to 25 versions of @valu N@, we define
-- the class VALU which generates them by typeclass resolution.
-- All of these should get inlined at compile time.

class VALU t b where

  valuN' :: b ~ IsBase t =>
            All EmbPrj (Domains t) =>
            t -> StrictProducts (Constant Int32 (Domains t)) -> R (CoDomain t)

  valueArgs :: b ~ IsBase t =>
               All EmbPrj (CoDomain t ': Domains t) =>
               Proxy t -> [Int32] -> Maybe (StrictProducts (Constant Int32 (Domains t)))

instance VALU t 'True where
  {-# INLINE valuN' #-}
  valuN' c () = return c

  {-# INLINE valueArgs #-}
  valueArgs _ xs = case xs of
    [] -> Just ()
    _  -> Nothing


instance VALU t (IsBase t) => VALU (a -> t) 'False where
  {-# INLINE valuN' #-}
  valuN' c (Pair a as) = do
    !v <- value a
    let !cv = c v
    valuN' cv as

  {-# INLINE valueArgs #-}
  valueArgs _ xs = case xs of
    x : xs' -> Pair x <$!> valueArgs (Proxy :: Proxy t) xs'
    _       -> Nothing

{-# INLINE valuN #-}
valuN :: forall t. VALU t (IsBase t) =>
         StrictCurrying (Constant Int32 (Domains t)) (R (CoDomain t)) =>
         All EmbPrj (Domains t) =>
         t -> Arrows (Constant Int32 (Domains t)) (R (CoDomain t))
valuN f = strictCurrys (Proxy :: Proxy (Constant Int32 (Domains t)))
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
