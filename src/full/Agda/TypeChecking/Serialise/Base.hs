{-# LANGUAGE CPP                  #-}
{-# LANGUAGE DataKinds            #-}
{-# LANGUAGE MagicHash            #-}
{-# LANGUAGE UnboxedTuples        #-}
{-# LANGUAGE UndecidableInstances #-} -- Due to ICODE vararg typeclass
{-# LANGUAGE PatternSynonyms      #-}

-- {-# options_ghc -ddump-to-file -ddump-simpl -dsuppress-all -dno-suppress-type-signatures #-}

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
import Data.Bits

import Data.Array.IArray
import Data.Array.IO
import qualified Data.HashMap.Strict as Hm
import qualified Data.ByteString.Lazy as L
import Data.Hashable
import Data.Word (Word32, Word64)
import Data.Maybe
import qualified Data.Binary as B
import qualified Data.Binary.Get as B
import qualified Data.Text      as T
import qualified Data.Text.Lazy as TL
import Data.Typeable ( cast, Typeable, TypeRep, typeRep, typeRepFingerprint )
import GHC.Exts (Word(..), timesWord2#, xor#, Any)
import GHC.Stack
import GHC.Fingerprint.Type
import Unsafe.Coerce

import Agda.Syntax.Common (NameId)
import Agda.Syntax.Internal (Term, QName(..), ModuleName(..), nameId)
import Agda.TypeChecking.Monad.Base.Types (ModuleToSource)

import Agda.Utils.FileName
import Agda.Utils.HashTable (HashTable)
import qualified Agda.Utils.HashTable as H
import Agda.Utils.IORef
import Agda.Utils.Lens
import Agda.Utils.List1 (List1)
import Agda.Utils.Monad
import Agda.Utils.TypeLevel
import Agda.Utils.VarSet (VarSet)
import Agda.Utils.Impossible

#include <MachDeps.h>


-- | Constructor tag (maybe omitted) and argument indices.
data Node
  = N0
  -- | N1 !Word32
  -- | N2# !Word64
  -- | N3# !Word64 !Word32
  -- | N4# !Word64 !Word64
  -- | N5# !Word64 !Word64 !Word32
  | (:*:) !Word32 !Node
  deriving Eq
infixr 5 :*:

splitW64 :: Word64 -> (Word32, Word32)
splitW64 x = let !a = fromIntegral (unsafeShiftR x 32)
                 !b = fromIntegral (x .&. 0x00000000ffffffff)
             in (a, b)
{-# inline splitW64 #-}

packW64 :: Word32 -> Word32 -> Word64
packW64 a b = unsafeShiftL (fromIntegral a) 32 .|. fromIntegral b
{-# inline packW64 #-}

-- pattern N2 :: Word32 -> Word32 -> Node
-- pattern N2 a b <- N2# (splitW64 -> (a, b)) where
--   N2 a b = N2# (packW64 a b)

-- pattern N3 :: Word32 -> Word32 -> Word32 -> Node
-- pattern N3 a b c <- N3# (splitW64 -> (a, b)) c where
--   N3 a b c = N3# (packW64 a b) c

-- pattern N4 :: Word32 -> Word32 -> Word32 -> Word32 -> Node
-- pattern N4 a b c d <- N4# (splitW64 -> (a, b)) (splitW64 -> (c, d)) where
--   N4 a b c d = N4# (packW64 a b) (packW64 c d)

-- pattern N5 :: Word32 -> Word32 -> Word32 -> Word32 -> Word32 -> Node
-- pattern N5 a b c d e <- N5# (splitW64 -> (a, b)) (splitW64 -> (c, d)) e where
--   N5 a b c d e = N5# (packW64 a b) (packW64 c d) e
-- {-# complete N0, N1, N2, N3, N4, N5, (:*:) #-}

pattern N1 :: Word32 -> Node
pattern N1 a = a :*: N0

pattern N2 :: Word32 -> Word32 -> Node
pattern N2 a b = a :*: b :*: N0

pattern N3 :: Word32 -> Word32 -> Word32 -> Node
pattern N3 a b c = a :*: b :*: c :*: N0

pattern N4 :: Word32 -> Word32 -> Word32 -> Word32 -> Node
pattern N4 a b c d = a :*: b :*: c :*: d :*: N0

pattern N5 :: Word32 -> Word32 -> Word32 -> Word32 -> Word32 -> Node
pattern N5 a b c d e = a :*: b :*: c :*: d :*: e :*: N0
{-# complete N0, N1, N2, N3, N4, N5, (:*:) #-}


instance Hashable Node where
  -- Adapted from https://github.com/tkaitchuck/aHash/wiki/AHash-fallback-algorithm
  hashWithSalt h n = fromIntegral (go (fromIntegral h) n) where
    xor (W# x) (W# y) = W# (xor# x y)

    foldedMul :: Word -> Word -> Word
    foldedMul (W# x) (W# y) = case timesWord2# x y of (# hi, lo #) -> W# (xor# hi lo)

    combine :: Word -> Word -> Word
    combine x y = foldedMul (xor x y) factor where
      -- We use a version of fibonacci hashing, where our multiplier is the
      -- nearest prime to 2^64/phi or 2^32/phi. See https://stackoverflow.com/q/4113278.
#if WORD_SIZE_IN_BITS == 64
      factor = 11400714819323198549
#else
      factor = 2654435741
#endif

    go :: Word -> Node -> Word
    go !h N0           = h
    -- go  h (N1 a)       = h `combine` fromIntegral a
    -- go  h (N2# a)      = h `combine` fromIntegral a
    -- go  h (N3# a b)    = h `combine` fromIntegral a `combine` fromIntegral b
    -- go  h (N4# a b)    = h `combine` fromIntegral a `combine` fromIntegral b
    -- go  h (N5# a b c)  = h `combine` fromIntegral a `combine` fromIntegral b `combine` fromIntegral c
    go  h ((:*:) n ns) = go (combine h (fromIntegral n)) ns

  hash = hashWithSalt seed where
#if WORD_SIZE_IN_BITS == 64
      seed = 3032525626373534813
#else
      seed = 1103515245
#endif

instance B.Binary Node where

  get = go =<< B.get where

    go :: Int -> B.Get Node
    go 0 = pure N0
    -- go 1 = do
    --   !a <- B.get
    --   pure $! N1 a
    -- go 2 = do
    --   !a <- B.get
    --   !b <- B.get
    --   pure $! N2 a b
    -- go 3 = do
    --   !a <- B.get
    --   !b <- B.get
    --   !c <- B.get
    --   pure $! N3 a b c
    -- go 4 = do
    --   !a <- B.get
    --   !b <- B.get
    --   !c <- B.get
    --   !d <- B.get
    --   pure $! N4 a b c d
    -- go 5 = do
    --   !a <- B.get
    --   !b <- B.get
    --   !c <- B.get
    --   !d <- B.get
    --   !e <- B.get
    --   pure $! N5 a b c d e
    go n = do
      !x    <- B.get
      !node <- go (n - 1)
      pure $! (:*:) x node

  put n = B.put (len n) <> go n where

    len :: Node -> Int
    len = go 0 where
      go !acc N0         = acc
      -- go acc  N1{}       = acc + 1
      -- go acc  N2#{}      = acc + 2
      -- go acc  N3#{}      = acc + 3
      -- go acc  N4#{}      = acc + 4
      -- go acc  N5#{}      = acc + 5
      go acc ((:*:) _ n) = go (acc + 1) n

    go :: Node -> B.Put
    go N0             = mempty
    -- go (N1 a)         = B.put a
    -- go (N2 a b)       = B.put a >> B.put b
    -- go (N3 a b c)     = B.put a >> B.put b >> B.put c
    -- go (N4 a b c d)   = B.put a >> B.put b >> B.put c >> B.put d
    -- go (N5 a b c d e) = B.put a >> B.put b >> B.put c >> B.put d >> B.put e
    go ((:*:) n ns)   = B.put n <> go ns

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

-- András: TODO: the NOINLINE + the function looks bad
lookupME :: forall a. Proxy a -> Fingerprint -> MemoEntry -> (# a | (# #) #)
lookupME proxy fprint me = go fprint me where
  go :: Fingerprint -> MemoEntry -> (# a | (# #) #)
  go fp MEEmpty =
    (# | (# #) #)
  go fp (MECons fp' x me)
    | fp == fp' = let res = unsafeCoerce x in (# res | #)
    | True      = go fp me
{-# NOINLINE lookupME #-}

-- | Structure providing fresh identifiers for hash map
--   and counting hash map hits (i.e. when no fresh identifier required).
#ifdef DEBUG_SERIALISATION
data FreshAndReuse = FreshAndReuse
  { farFresh :: !Word32 -- ^ Number of hash map misses.
  , farReuse :: !Word32 -- ^ Number of hash map hits.
  }
#else
newtype FreshAndReuse = FreshAndReuse
  { farFresh :: Word32 -- ^ Number of hash map misses.
  }
#endif

farEmpty :: FreshAndReuse
farEmpty = FreshAndReuse 0
#ifdef DEBUG_SERIALISATION
                           0
#endif

lensFresh :: Lens' FreshAndReuse Word32
lensFresh f r = f (farFresh r) <&> \ i -> r { farFresh = i }
{-# INLINE lensFresh #-}

#ifdef DEBUG_SERIALISATION
lensReuse :: Lens' FreshAndReuse Word32
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
  { nodeD        :: !(HashTable Node    Word32)    -- ^ Written to interface file.
  , stringD      :: !(HashTable String  Word32)    -- ^ Written to interface file.
  , lTextD       :: !(HashTable TL.Text Word32)    -- ^ Written to interface file.
  , sTextD       :: !(HashTable T.Text  Word32)    -- ^ Written to interface file.
  , integerD     :: !(HashTable Integer Word32)    -- ^ Written to interface file.
  , varSetD      :: !(HashTable VarSet Word32)    -- ^ Written to interface file.
  , doubleD      :: !(HashTable Double  Word32)    -- ^ Written to interface file.
  -- Dicitionaries which are not serialized, but provide
  -- short cuts to speed up serialization:
  -- Andreas, Makoto, AIM XXI
  -- Memoizing A.Name does not buy us much if we already memoize A.QName.
  , nameD        :: !(HashTable NameId  Word32)    -- ^ Not written to interface file.
  , qnameD       :: !(HashTable QNameId Word32)    -- ^ Not written to interface file.
  -- Fresh UIDs and reuse statistics:
  , nodeC        :: !(IORef FreshAndReuse)  -- counters for fresh indexes
  , stringC      :: !(IORef FreshAndReuse)
  , lTextC       :: !(IORef FreshAndReuse)
  , sTextC       :: !(IORef FreshAndReuse)
  , integerC     :: !(IORef FreshAndReuse)
  , varSetC      :: !(IORef FreshAndReuse)
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
  <*> newIORef farEmpty
  <*> H.empty
  <*> pure collectStats

-- | Univeral memo structure, to introduce sharing during decoding
type Memo = IOArray Word32 MemoEntry

-- data DecodeCold = DecodeCold {


-- | Decoder arguments.
data Decode = Decode
  { nodeE     :: !(Array Word32 Node)     -- ^ Obtained from interface file.
  , stringE   :: !(Array Word32 String)   -- ^ Obtained from interface file.
  , lTextE    :: !(Array Word32 TL.Text)  -- ^ Obtained from interface file.
  , sTextE    :: !(Array Word32 T.Text)   -- ^ Obtained from interface file.
  , integerE  :: !(Array Word32 Integer)  -- ^ Obtained from interface file.
  , varSetE   :: !(Array Word32 VarSet)   -- ^ Obtained from interface file.
  , doubleE   :: !(Array Word32 Double)   -- ^ Obtained from interface file.
  , nodeMemo  :: {-# unpack #-} !Memo
    -- ^ Created and modified by decoder.
    --   Used to introduce sharing while deserializing objects.
  , modFile   :: !(IORef ModuleToSource)
    -- ^ Maps module names to file names. Constructed by the decoder.
  , includes  :: !(List1 AbsolutePath)
    -- ^ The include directories.
  }

-- | Monad used by the encoder.

type S a = ReaderT Dict IO a

-- | Monad used by the decoder.
--
-- 'TCM' is not used because the associated overheads would make
-- decoding slower.

type R = ReaderT Decode IO

-- | Throws an error which is suitable when the data stream is
-- malformed.

malformed :: HasCallStack => R a
malformed = __IMPOSSIBLE__ -- liftIO $ E.throwIO $ E.ErrorCall "Malformed input."
{-# NOINLINE malformed #-} -- 2023-10-2 András: cold code, so should be out-of-line.

class Typeable a => EmbPrj a where
  icode :: a -> S Word32  -- ^ Serialization (wrapper).
  icod_ :: a -> S Word32  -- ^ Serialization (worker).
  value :: Word32 -> R a  -- ^ Deserialization.

  icode a = do
    !r <- icod_ a
    tickICode a
    pure r
  {-# INLINE icode #-}

  -- Simple enumeration types can be (de)serialized using (from/to)Enum.
  default value :: (Enum a, Bounded a) => Word32 -> R a
  value i =
    let i' = fromIntegral i in
    if i' >= fromEnum (minBound :: a) && i' <= fromEnum (maxBound :: a)
    then pure $! toEnum i'
    else malformed

  default icod_ :: (Enum a, Bounded a) => a -> S Word32
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
--   =  (Dict -> HashTable k Word32)
--   -> (Dict -> IORef Word32)
--   -> k -> S Word32
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
  =>  (Dict -> HashTable k Word32)
  -> (Dict -> IORef FreshAndReuse)
  -> k -> S Word32
icodeX dict counter key = do
  d <- asks dict
  c <- asks counter
  liftIO $ do
    mi <- H.lookup d key
    case mi of
      Just i  -> do
#ifdef DEBUG_SERIALISATION
        modifyIORef' c $ over lensReuse (+ 1)
#endif
        return $! i
      Nothing -> do
        !fresh <- (^. lensFresh) <$> do readModifyIORef' c $ over lensFresh (+ 1)
        H.insert d key fresh
        return fresh

-- Instead of inlining icodeX, we manually specialize it to
-- its five uses: Integer, VarSet, String, Double, Node.
-- Not a great gain (hardly noticeable), but not harmful.

icodeInteger :: Integer -> S Word32
icodeInteger key = do
  d <- asks integerD
  c <- asks integerC
  liftIO $ do
    mi <- H.lookup d key
    case mi of
      Just i  -> do
#ifdef DEBUG_SERIALISATION
        modifyIORef' c $ over lensReuse (+ 1)
#endif
        return $! i
      Nothing -> do
        !fresh <- (^. lensFresh) <$> do readModifyIORef' c $ over lensFresh (+ 1)
        H.insert d key fresh
        return fresh

icodeVarSet :: VarSet -> S Word32
icodeVarSet key = do
  d <- asks varSetD
  c <- asks varSetC
  liftIO $ do
    mi <- H.lookup d key
    case mi of
      Just i  -> do
#ifdef DEBUG_SERIALISATION
        modifyIORef' c $ over lensReuse (+ 1)
#endif
        return $! i
      Nothing -> do
        !fresh <- (^. lensFresh) <$> do readModifyIORef' c $ over lensFresh (+ 1)
        H.insert d key fresh
        return fresh

icodeDouble :: Double -> S Word32
icodeDouble key = do
  d <- asks doubleD
  c <- asks doubleC
  liftIO $ do
    mi <- H.lookup d key
    case mi of
      Just i  -> do
#ifdef DEBUG_SERIALISATION
        modifyIORef' c $ over lensReuse (+ 1)
#endif
        return $! i
      Nothing -> do
        !fresh <- (^. lensFresh) <$> do readModifyIORef' c $ over lensFresh (+ 1)
        H.insert d key fresh
        return fresh

icodeString :: String -> S Word32
icodeString key = do
  d <- asks stringD
  c <- asks stringC
  liftIO $ do
    mi <- H.lookup d key
    case mi of
      Just i  -> do
#ifdef DEBUG_SERIALISATION
        modifyIORef' c $ over lensReuse (+ 1)
#endif
        return i
      Nothing -> do
        !fresh <- (^. lensFresh) <$> do readModifyIORef' c $ over lensFresh (+ 1)
        H.insert d key fresh
        return fresh

icodeNode :: Node -> S Word32
icodeNode key = do
  d <- asks nodeD
  c <- asks nodeC
  liftIO $ do
    mi <- H.lookup d key
    case mi of
      Just i  -> do
#ifdef DEBUG_SERIALISATION
        modifyIORef' c $ over lensReuse (+ 1)
#endif
        return $! i
      Nothing -> do
        !fresh <- (^. lensFresh) <$> do readModifyIORef' c $ over lensFresh (+ 1)
        H.insert d key fresh
        return fresh

-- icodeN :: [Word32] -> S Word32
-- icodeN = icodeX nodeD nodeC

-- | @icode@ only if thing has not seen before.
icodeMemo
  :: (Ord a, Hashable a)
  => (Dict -> HashTable a Word32)    -- ^ Memo structure for thing of key @a@.
  -> (Dict -> IORef FreshAndReuse)  -- ^ Statistics.
  -> a        -- ^ Key to the thing.
  -> S Word32  -- ^ Fallback computation to encode the thing.
  -> S Word32  -- ^ Encoded thing.
icodeMemo getDict getCounter a icodeP = do
    h  <- asks getDict
    mi <- liftIO $ H.lookup h a
    st <- asks getCounter
    case mi of
      Just i  -> liftIO $ do
#ifdef DEBUG_SERIALISATION
        modifyIORef' st $ over lensReuse (+ 1)
#endif
        return $! i
      Nothing -> do
        liftIO $ modifyIORef' st $ over lensFresh (+ 1)
        !i <- icodeP
        liftIO $ H.insert h a i
        return i

{-# INLINE vcase #-}
-- | @vcase value ix@ decodes thing represented by @ix :: Word32@
--   via the @valu@ function and stores it in 'nodeMemo'.
--   If @ix@ is present in 'nodeMemo', @valu@ is not used, but
--   the thing is read from 'nodeMemo' instead.
vcase :: forall a . EmbPrj a => (Node -> R a) -> Word32 -> R a
vcase valu = \ix -> do
    memo <- asks nodeMemo
    let fp = fingerprintNoinline (typeRep (Proxy :: Proxy a))
    -- to introduce sharing, see if we have seen a thing
    -- represented by ix before
    slot <- liftIO $ readArray memo ix
    case lookupME (Proxy :: Proxy a) fp slot of
      -- use the stored value
      (# a | #) ->
        pure a
      _         ->
        -- read new value and save it
        do !v <- valu . (! ix) =<< asks nodeE
           liftIO $ writeArray memo ix $! MECons fp (unsafeCoerce v) slot
           return v


-- Arity-generic functions
----------------------------------------------------------------------------------------------------

-- | @icodeArgs proxy (a1, ..., an)@ maps @icode@ over @a1@, ..., @an@
--   and returns the corresponding list of @Word32@.
class ICODE t (a :: Nat) where
  icodeArgs :: Arity t ~ a => All EmbPrj (Domains t) =>
               Proxy t -> StrictProducts (Domains t) -> S Node

instance ICODE t 'Zero where
  icodeArgs _ _  = return N0
  {-# INLINE icodeArgs #-}

-- instance ICODE (a -> t) ('Suc 'Zero) where
--   icodeArgs _ (Pair a _) = do
--     !a <- icode a
--     pure $ N1 a
--   {-# INLINE icodeArgs #-}

-- instance ICODE (a -> b -> t) ('Suc ('Suc 'Zero)) where
--   icodeArgs _ (Pair a (Pair b _)) = do
--     !a <- icode a
--     !b <- icode b
--     pure $ N2 a b
--   {-# INLINE icodeArgs #-}

-- instance ICODE (a -> b -> c -> t) ('Suc ('Suc ('Suc 'Zero))) where
--   icodeArgs _ (Pair a (Pair b (Pair c _))) = do
--     !a <- icode a
--     !b <- icode b
--     !c <- icode c
--     pure $ N3 a b c
--   {-# INLINE icodeArgs #-}

-- instance ICODE (a -> b -> c -> d -> t) ('Suc ('Suc ('Suc ('Suc 'Zero)))) where
--   icodeArgs _ (Pair a (Pair b (Pair c (Pair d _)))) = do
--     !a <- icode a
--     !b <- icode b
--     !c <- icode c
--     !d <- icode d
--     pure $ N4 a b c d
--   {-# INLINE icodeArgs #-}

-- instance ICODE (a -> b -> c -> d -> e -> t) ('Suc ('Suc ('Suc ('Suc ('Suc 'Zero))))) where
--   icodeArgs _ (Pair a (Pair b (Pair c (Pair d (Pair e _))))) = do
--     !a <- icode a
--     !b <- icode b
--     !c <- icode c
--     !d <- icode d
--     !e <- icode e
--     pure $ N5 a b c d e
--   {-# INLINE icodeArgs #-}

instance ICODE t n
      => ICODE (a -> t) ('Suc n) where
  icodeArgs _ (Pair a as) = do
    !hd   <- icode a
    !node <- icodeArgs (Proxy :: Proxy t) as
    pure $ (:*:) hd node
  {-# INLINE icodeArgs #-}

-- instance ICODE t ('Suc ('Suc ('Suc ('Suc ('Suc n)))))
--       => ICODE (a -> t) ('Suc ('Suc ('Suc ('Suc ('Suc ('Suc n)))))) where
--   icodeArgs _ (Pair a as) = do
--     !hd   <- icode a
--     !node <- icodeArgs (Proxy :: Proxy t) as
--     pure $ (:*:) hd node
--   {-# INLINE icodeArgs #-}

-- -- | @icodeN tag t a1 ... an@ serialises the arguments @a1@, ..., @an@ of the
-- --   constructor @t@ together with a tag @tag@ picked to disambiguate between
-- --   different constructors.
-- --   It corresponds to @icodeNode . (tag :) =<< mapM icode [a1, ..., an]@

{-# INLINE icodeN #-}
icodeN :: forall t. ICODE (Word32 -> t) (Arity (Word32 -> t))
       => StrictCurrying (Domains (Word32 -> t)) (S Word32)
       => All EmbPrj (Domains (Word32 -> t)) =>
          Word32 -> t -> Arrows (Domains t) (S Word32)
icodeN tag _ =
   strictCurrys
      (Proxy :: Proxy (Domains (Word32 -> t)))
      (Proxy :: Proxy (S Word32))
      (\ !args -> do !node <- icodeArgs (Proxy :: Proxy (Word32 -> t)) args
                     icodeNode node)
      tag

-- | @icodeN'@ is the same as @icodeN@ except that there is no tag
{-# INLINE icodeN' #-}
icodeN' :: forall t. ICODE t (Arity t) => StrictCurrying (Domains t) (S Word32) =>
           All EmbPrj (Domains t) =>
           t -> Arrows (Domains t) (S Word32)
icodeN' _ =
  strictCurrys (Proxy :: Proxy (Domains t)) (Proxy :: Proxy (S Word32)) $ \ !args -> do
    !node <- icodeArgs (Proxy :: Proxy t) args
    icodeNode node


-- Instead of having up to 25 versions of @valu N@, we define
-- the class VALU which generates them by typeclass resolution.
-- All of these should get inlined at compile time.

class VALU t (a :: Nat) where
  valuN' :: a ~ Arity t =>
            All EmbPrj (Domains t) =>
            t -> StrictProducts (Constant Word32 (Domains t)) -> R (CoDomain t)

  valueArgs :: a ~ Arity t =>
               All EmbPrj (CoDomain t ': Domains t) =>
               Proxy t -> Node -> Maybe (StrictProducts (Constant Word32 (Domains t)))

instance VALU t 'Zero where
  {-# INLINE valuN' #-}
  valuN' f _ = return f
  {-# INLINE valueArgs #-}
  valueArgs _ xs = case xs of
    N0 -> Just ()
    _  -> Nothing

-- instance VALU (a -> t) ('Suc 'Zero) where
--   {-# INLINE valuN' #-}
--   valuN' f (Pair a _) = do
--     !a <- value a
--     return $! f a
--   {-# INLINE valueArgs #-}
--   valueArgs _ xs = case xs of
--     N1 a -> Just (Pair a ())
--     _    -> Nothing

-- instance VALU (a -> b -> t) ('Suc ('Suc 'Zero)) where
--   {-# INLINE valuN' #-}
--   valuN' f (Pair a (Pair b _)) = do
--     !a <- value a
--     !b <- value b
--     return $! f a b
--   {-# INLINE valueArgs #-}
--   valueArgs _ xs = case xs of
--     N2 a b -> Just (Pair a (Pair b ()))
--     _      -> Nothing

-- instance VALU (a -> b -> c -> t) ('Suc ('Suc ('Suc 'Zero))) where
--   {-# INLINE valuN' #-}
--   valuN' f (Pair a (Pair b (Pair c _))) = do
--     !a <- value a
--     !b <- value b
--     !c <- value c
--     return $! f a b c
--   {-# INLINE valueArgs #-}
--   valueArgs _ xs = case xs of
--     N3 a b c -> Just (Pair a (Pair b (Pair c ())))
--     _        -> Nothing

-- instance VALU (a -> b -> c -> d -> t) ('Suc ('Suc ('Suc ('Suc 'Zero)))) where
--   {-# INLINE valuN' #-}
--   valuN' f (Pair a (Pair b (Pair c (Pair d _)))) = do
--     !a <- value a
--     !b <- value b
--     !c <- value c
--     !d <- value d
--     return $! f a b c d
--   {-# INLINE valueArgs #-}
--   valueArgs _ xs = case xs of
--     N4 a b c d -> Just (Pair a (Pair b (Pair c (Pair d ()))))
--     _          -> Nothing

-- instance VALU (a -> b -> c -> d -> e -> t) ('Suc ('Suc ('Suc ('Suc ('Suc 'Zero))))) where
--   {-# INLINE valuN' #-}
--   valuN' f (Pair a (Pair b (Pair c (Pair d (Pair e _))))) = do
--     !a <- value a
--     !b <- value b
--     !c <- value c
--     !d <- value d
--     !e <- value e
--     return $! f a b c d e
--   {-# INLINE valueArgs #-}
--   valueArgs _ xs = case xs of
--     N5 a b c d e -> Just (Pair a (Pair b (Pair c (Pair d (Pair e ())))))
--     _            -> Nothing

-- instance VALU t ('Suc ('Suc ('Suc ('Suc ('Suc n)))))
--       => VALU (a -> t) ('Suc ('Suc ('Suc ('Suc ('Suc ('Suc n)))))) where
--   {-# INLINE valuN' #-}
--   valuN' f (Pair a as) = do
--     !a <- value a
--     let !fv = f a
--     valuN' fv as

--   {-# INLINE valueArgs #-}
--   valueArgs _ xs = case xs of
--     x :*: xs' -> Pair x <$!> valueArgs (Proxy :: Proxy t) xs'
--     _         -> Nothing


instance VALU t n
      => VALU (a -> t) ('Suc n) where
  {-# INLINE valuN' #-}
  valuN' f (Pair a as) = do
    !a <- value a
    let !fv = f a
    valuN' fv as

  {-# INLINE valueArgs #-}
  valueArgs _ xs = case xs of
    x :*: xs' -> Pair x <$!> valueArgs (Proxy :: Proxy t) xs'
    _         -> Nothing

--------------------------------------------------------------------------------


{-# INLINE valuN #-}
valuN :: forall t. VALU t (Arity t) =>
         StrictCurrying (Constant Word32 (Domains t)) (R (CoDomain t)) =>
         All EmbPrj (Domains t) =>
         t -> Arrows (Constant Word32 (Domains t)) (R (CoDomain t))
valuN f = strictCurrys (Proxy :: Proxy (Constant Word32 (Domains t)))
                 (Proxy :: Proxy (R (CoDomain t)))
                 (valuN' f)

{-# INLINE valueN #-}
valueN :: forall t. VALU t (Arity t) =>
          All EmbPrj (CoDomain t ': Domains t) =>
          t -> Word32 -> R (CoDomain t)
valueN t = vcase valu where
  valu int32s = case valueArgs (Proxy :: Proxy t) int32s of
                  Nothing -> malformed
                  Just vs -> valuN' t vs
