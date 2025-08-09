{-# LANGUAGE CPP                  #-}
{-# LANGUAGE DataKinds            #-}
{-# LANGUAGE MagicHash            #-}
{-# LANGUAGE UnboxedTuples        #-}
{-# LANGUAGE UndecidableInstances #-} -- Due to ICODE vararg typeclass
{-# LANGUAGE PatternSynonyms      #-}

{-# options_ghc -ddump-to-file -ddump-simpl -dsuppress-all -dno-suppress-type-signatures #-}

{-
András, 2023-10-2:

All code in Agda/TypeChecking/Serialise should be strict, since serialization necessarily
forces all data, eventually.
  - (<$!>) should be used instead of lazy fmap.
  - Any redex that's passed to `return`, a lazy constructor, or a function, should
    be forced beforehand with strict `let`, strict binding or ($!).
-}

module Agda.TypeChecking.Serialise.Base (
    module Agda.TypeChecking.Serialise.Node
  , module Agda.TypeChecking.Serialise.Base
  ) where

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
import qualified Data.Text      as T
import qualified Data.Text.Lazy as TL
import Data.Typeable ( cast, Typeable, TypeRep, typeRep, typeRepFingerprint )
import GHC.Exts
import GHC.Stack
import GHC.Fingerprint.Type
import Unsafe.Coerce

import Agda.Syntax.Common (NameId)
import Agda.Syntax.Internal (Term, QName(..), ModuleName(..), nameId)
import Agda.TypeChecking.Monad.Base.Types (ModuleToSource)
import Agda.TypeChecking.Serialise.Node

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
import qualified Agda.Utils.MinimalArray.MutablePrim as MP
import qualified Agda.Utils.MinimalArray.Lifted as AL
import qualified Agda.Utils.MinimalArray.MutableLifted as ML

--------------------------------------------------------------------------------

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

lookupME :: forall a. Proxy a -> Fingerprint -> MemoEntry -> (# a | (# #) #)
lookupME proxy fprint me = go fprint me where
  go :: Fingerprint -> MemoEntry -> (# a | (# #) #)
  go fp MEEmpty =
    (# | (# #) #)
  go fp (MECons fp' x me)
    | fp == fp' = let res = unsafeCoerce x in (# res | #)
    | True      = go fp me
{-# NOINLINE lookupME #-}

type FreshAndReuse = MP.IOArray Word32

{-# INLINE bumpFresh #-}
bumpFresh :: FreshAndReuse -> IO Word32
bumpFresh arr = do
  !n <- MP.unsafeRead arr 0
  MP.unsafeWrite arr 0 (n + 1)
  pure n

{-# INLINE bumpReuse #-}
bumpReuse :: FreshAndReuse -> IO Word32
bumpReuse arr = do
  !n <- MP.unsafeRead arr 1
  MP.unsafeWrite arr 1 (n + 1)
  pure n

farEmpty :: IO FreshAndReuse
farEmpty = do
  arr <- MP.new 2
  MP.unsafeWrite arr 0 0
  MP.unsafeWrite arr 1 0
  pure arr

getFresh :: FreshAndReuse -> IO Word32
getFresh far = MP.unsafeRead far 0

getReuse :: FreshAndReuse -> IO Word32
getReuse far = MP.unsafeRead far 1

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
  , nodeC        :: !(FreshAndReuse)  -- counters for fresh indexes
  , stringC      :: !(FreshAndReuse)
  , lTextC       :: !(FreshAndReuse)
  , sTextC       :: !(FreshAndReuse)
  , integerC     :: !(FreshAndReuse)
  , varSetC      :: !(FreshAndReuse)
  , doubleC      :: !(FreshAndReuse)
  , termC        :: !(FreshAndReuse)
  , nameC        :: !(FreshAndReuse)
  , qnameC       :: !(FreshAndReuse)
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
  <*> farEmpty
  <*> farEmpty
  <*> farEmpty
  <*> farEmpty
  <*> farEmpty
  <*> farEmpty
  <*> farEmpty
  <*> farEmpty
  <*> farEmpty
  <*> farEmpty
  <*> H.empty
  <*> pure collectStats

-- | Decoder arguments.
data Decode = Decode
  { nodeA     :: !(AL.Array Node)     -- ^ Obtained from interface.
  , stringA   :: !(AL.Array String)   -- ^ Obtained from interface.
  , lTextA    :: !(AL.Array TL.Text)  -- ^ Obtained from interface.
  , sTextA    :: !(AL.Array T.Text)   -- ^ Obtained from interface.
  , integerA  :: !(AL.Array Integer)  -- ^ Obtained from interface.
  , varSetA   :: !(AL.Array VarSet)   -- ^ Obtained from interface.
  , doubleA   :: !(AL.Array Double)   -- ^ Obtained from interface.
  , nodeMemo  :: !(ML.IOArray MemoEntry)
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

malformedIO :: HasCallStack => IO a
malformedIO = __IMPOSSIBLE__
{-# NOINLINE malformedIO #-}

class Typeable a => EmbPrj a where
  icode :: a -> S Word32  -- ^ Serialization (wrapper).
  icod_ :: a -> S Word32  -- ^ Serialization (worker).
  value :: Word32 -> R a  -- ^ Deserialization.

  -- icode a = icod_ a
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
  => (Dict -> HashTable k Word32)
  -> (Dict -> FreshAndReuse)
  -> k -> S Word32
icodeX dict counter key = do
  d <- asks dict
  c <- asks counter
  liftIO $ do
    mi <- H.lookup d key
    case mi of
      Just i  -> do
#ifdef DEBUG_SERIALISATION
        liftIO $ bumpReuse c
#endif
        return $! i
      Nothing -> do
        !fresh <- liftIO $ bumpFresh c
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
        liftIO $ bumpReuse c
#endif
        return $! i
      Nothing -> do
        !fresh <- liftIO $ bumpFresh c
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
        liftIO $ bumpReuse c
#endif
        return $! i
      Nothing -> do
        !fresh <- liftIO $ bumpFresh c
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
        liftIO $ bumpReuse c
#endif
        return $! i
      Nothing -> do
        !fresh <- liftIO $ bumpFresh c
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
        liftIO $ bumpReuse c
#endif
        return i
      Nothing -> do
        !fresh <- liftIO $ bumpFresh c
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
        liftIO $ bumpReuse c
#endif
        return $! i
      Nothing -> do
        !fresh <- liftIO $ bumpFresh c
        H.insert d key fresh
        return fresh

-- | @icode@ only if thing has not seen before.
icodeMemo
  :: (Ord a, Hashable a)
  => (Dict -> HashTable a Word32)    -- ^ Memo structure for thing of key @a@.
  -> (Dict -> FreshAndReuse)         -- ^ Counter and statistics.
  -> a        -- ^ Key to the thing.
  -> S Word32  -- ^ Fallback computation to encode the thing.
  -> S Word32  -- ^ Encoded thing.
icodeMemo getDict getCounter a icodeP = do
    h  <- asks getDict
    mi <- liftIO $ H.lookup h a
    c  <- asks getCounter
    case mi of
      Just i  -> liftIO $ do
#ifdef DEBUG_SERIALISATION
        liftIO $ bumpReuse c
#endif
        return $! i
      Nothing -> do
        !fresh <- liftIO $ bumpFresh c
        !i <- icodeP
        liftIO $ H.insert h a i
        return i

{-# INLINE vcase #-}
-- | @vcase value ix@ decodes thing represented by @ix :: Word32@
--   via the @valu@ function and stores it in 'nodeMemo'.
--   If @ix@ is present in 'nodeMemo', @valu@ is not used, but
--   the thing is read from 'nodeMemo' instead.
vcase :: forall a . EmbPrj a => (Node -> R a) -> Word32 -> R a
vcase valu = \ix -> ReaderT \dict -> do
    let !memo = nodeMemo dict

    let !fp = fingerprintNoinline (typeRep (Proxy :: Proxy a))
    -- to introduce sharing, see if we have seen a thing
    -- represented by ix before
    let !iix = fromIntegral ix :: Int
    !slot <- ML.read memo iix
    case lookupME (Proxy :: Proxy a) fp slot of
      -- use the stored value
      (# a | #) ->
        pure a
      _         ->
        -- read new value and save it
        do !v <- runReaderT (valu (AL.index (nodeA dict) iix)) dict
           ML.write memo iix $! MECons fp (unsafeCoerce v) slot
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

instance ICODE (a -> t) ('Suc 'Zero) where
  icodeArgs _ (Pair a _) = do
    !a <- icode a
    pure $ N1 a
  {-# INLINE icodeArgs #-}

instance ICODE (a -> b -> t) ('Suc ('Suc 'Zero)) where
  icodeArgs _ (Pair a (Pair b _)) = do
    !a <- icode a
    !b <- icode b
    pure $ N2 a b
  {-# INLINE icodeArgs #-}

instance ICODE (a -> b -> c -> t) ('Suc ('Suc ('Suc 'Zero))) where
  icodeArgs _ (Pair a (Pair b (Pair c _))) = do
    !a <- icode a
    !b <- icode b
    !c <- icode c
    pure $ N3 a b c
  {-# INLINE icodeArgs #-}

instance ICODE (a -> b -> c -> d -> t) ('Suc ('Suc ('Suc ('Suc 'Zero)))) where
  icodeArgs _ (Pair a (Pair b (Pair c (Pair d _)))) = do
    !a <- icode a
    !b <- icode b
    !c <- icode c
    !d <- icode d
    pure $ N4 a b c d
  {-# INLINE icodeArgs #-}

instance ICODE (a -> b -> c -> d -> e -> t) ('Suc ('Suc ('Suc ('Suc ('Suc 'Zero))))) where
  icodeArgs _ (Pair a (Pair b (Pair c (Pair d (Pair e _))))) = do
    !a <- icode a
    !b <- icode b
    !c <- icode c
    !d <- icode d
    !e <- icode e
    pure $ N5 a b c d e
  {-# INLINE icodeArgs #-}

instance ICODE t ('Suc ('Suc ('Suc ('Suc ('Suc n)))))
      => ICODE (a -> t) ('Suc ('Suc ('Suc ('Suc ('Suc ('Suc n)))))) where
  icodeArgs _ (Pair a as) = do
    !hd   <- icode a
    !node <- icodeArgs (Proxy :: Proxy t) as
    pure $ (:*:) hd node
  {-# INLINE icodeArgs #-}

-- | @icodeN tag t a1 ... an@ serialises the arguments @a1@, ..., @an@ of the
--   constructor @t@ together with a tag @tag@ picked to disambiguate between
--   different constructors.
--   It corresponds to @icodeNode . (tag :) =<< mapM icode [a1, ..., an]@

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

instance VALU (a -> t) ('Suc 'Zero) where
  {-# INLINE valuN' #-}
  valuN' f (Pair a _) = do
    !a <- value a
    return $! f a
  {-# INLINE valueArgs #-}
  valueArgs _ xs = case xs of
    N1 a -> Just (Pair a ())
    _    -> Nothing

instance VALU (a -> b -> t) ('Suc ('Suc 'Zero)) where
  {-# INLINE valuN' #-}
  valuN' f (Pair a (Pair b _)) = do
    !a <- value a
    !b <- value b
    return $! f a b
  {-# INLINE valueArgs #-}
  valueArgs _ xs = case xs of
    N2 a b -> Just (Pair a (Pair b ()))
    _      -> Nothing

instance VALU (a -> b -> c -> t) ('Suc ('Suc ('Suc 'Zero))) where
  {-# INLINE valuN' #-}
  valuN' f (Pair a (Pair b (Pair c _))) = do
    !a <- value a
    !b <- value b
    !c <- value c
    return $! f a b c
  {-# INLINE valueArgs #-}
  valueArgs _ xs = case xs of
    N3 a b c -> Just (Pair a (Pair b (Pair c ())))
    _        -> Nothing

instance VALU (a -> b -> c -> d -> t) ('Suc ('Suc ('Suc ('Suc 'Zero)))) where
  {-# INLINE valuN' #-}
  valuN' f (Pair a (Pair b (Pair c (Pair d _)))) = do
    !a <- value a
    !b <- value b
    !c <- value c
    !d <- value d
    return $! f a b c d
  {-# INLINE valueArgs #-}
  valueArgs _ xs = case xs of
    N4 a b c d -> Just (Pair a (Pair b (Pair c (Pair d ()))))
    _          -> Nothing

instance VALU (a -> b -> c -> d -> e -> t) ('Suc ('Suc ('Suc ('Suc ('Suc 'Zero))))) where
  {-# INLINE valuN' #-}
  valuN' f (Pair a (Pair b (Pair c (Pair d (Pair e _))))) = do
    !a <- value a
    !b <- value b
    !c <- value c
    !d <- value d
    !e <- value e
    return $! f a b c d e
  {-# INLINE valueArgs #-}
  valueArgs _ xs = case xs of
    N5 a b c d e -> Just (Pair a (Pair b (Pair c (Pair d (Pair e ())))))
    _            -> Nothing

instance VALU t ('Suc ('Suc ('Suc ('Suc ('Suc n)))))
      => VALU (a -> t) ('Suc ('Suc ('Suc ('Suc ('Suc ('Suc n)))))) where
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
