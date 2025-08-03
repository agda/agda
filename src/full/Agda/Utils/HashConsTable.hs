{-# LANGUAGE
    Strict
  , MagicHash
  , UnboxedTuples
  , RoleAnnotations
  , TypeApplications
  #-}

{-# OPTIONS_GHC -Wno-redundant-bang-patterns #-}

module Agda.Utils.HashConsTable (
    Table
  , new
  , Agda.Utils.HashConsTable.toList
  , insertLookup
  , size
  ) where

import Control.Monad
import GHC.Exts
import Data.Hashable
import Data.Word
import Data.Bits
import Data.Kind
import GHC.Types
import Debug.Trace

import qualified Agda.Utils.MinimalArray.Lifted as L
import qualified Agda.Utils.MinimalArray.MutableLifted as ML
import qualified Agda.Utils.MinimalArray.Prim as P
import qualified Agda.Utils.MinimalArray.MutablePrim as MP

import Data.Primitive.Types
import Control.Monad.Primitive

type role Table representational
data Table (k :: Type) = Table {unTable :: MutableArrayArray# RealWorld}

initialCapacity :: Int
initialCapacity = 32

{-# INLINE newTableRef #-}
newTableRef :: IO (Table k)
newTableRef = IO \s -> case newArrayArray# 3# s of
  (# s, arr #) -> (# s, Table arr #)

{-# INLINE getSizeRef #-}
getSizeRef :: Table k -> IO (MP.IOArray Int)
getSizeRef (Table arr) = IO \s -> case readArrayArrayArray# arr 0# s of
  (# s, arr #) -> (# s, MP.Array (unsafeCoerce# arr) #)

{-# INLINE getKeys #-}
getKeys :: Table k -> IO (ML.IOArray k)
getKeys (Table arr) = IO \s -> case readArrayArrayArray# arr 1# s of
  (# s, arr #) -> (# s, ML.Array (unsafeCoerce# arr) #)

{-# INLINE getVals #-}
getVals :: Table k -> IO (MP.IOArray Word64)
getVals (Table arr) = IO \s -> case readArrayArrayArray# arr 2# s of
  (# s, arr #) -> (# s, MP.Array (unsafeCoerce# arr) #)

{-# INLINE setSizeRef #-}
setSizeRef :: Table k -> MP.IOArray Int -> IO ()
setSizeRef (Table arr) (MP.Array sizeRef) =
  IO \s -> case writeArrayArrayArray# arr 0# (unsafeCoerce# sizeRef) s of
    s -> (# s, () #)

{-# INLINE setKeys #-}
setKeys :: Table k -> ML.IOArray k -> IO ()
setKeys (Table arr) (ML.Array keys) =
  IO \s -> case writeArrayArrayArray# arr 1# (unsafeCoerce# keys) s of
    s -> (# s, () #)

{-# INLINE setVals #-}
setVals :: Table k -> MP.IOArray Word64 -> IO ()
setVals (Table arr) (MP.Array vals) =
  IO \s -> case writeArrayArrayArray# arr 2# (unsafeCoerce# vals) s of
    s -> (# s, () #)

{-# INLINE ptrEq #-}
ptrEq :: a -> a -> Bool
ptrEq !x !y = isTrue# (reallyUnsafePtrEquality# x y)

{-# INLINE ctzInt #-}
ctzInt :: Int -> Int
ctzInt (I# n) = I# (word2Int# (ctz# (int2Word# n)))

{-# INLINE splitW64 #-}
splitW64 :: Word64 -> (Word32, Word32)
splitW64 x = let !a = fromIntegral (unsafeShiftR x 32)
                 !b = fromIntegral (x .&. 0x00000000ffffffff)
             in (a, b)

newVals :: Int -> IO (MP.IOArray Word64)
newVals cap = do
  arr <- MP.new @Word64 cap
  MP.set arr (packW64 0 maxBound)
  pure arr

{-# INLINE packW64 #-}
packW64 :: Word32 -> Word32 -> Word64
packW64 a b = unsafeShiftL (fromIntegral a) 32 .|. fromIntegral b

{-# NOINLINE undefElem #-}
undefElem :: a
undefElem = error "HashConsTable: undefined element"

new :: forall k. IO (Table k)
new = do
  sizeRef <- MP.new @Int 1
  MP.unsafeWrite sizeRef 0 0
  keys <- ML.new @k initialCapacity undefElem
  vals <- newVals initialCapacity
  tbl  <- newTableRef
  setSizeRef tbl sizeRef
  setKeys tbl keys
  setVals tbl vals
  pure tbl

{-# INLINE size #-}
size :: Table k -> IO Int
size t = do
  sizeRef <- getSizeRef t
  MP.unsafeRead sizeRef 0

{-# NOINLINE growTable #-}
growTable :: forall k. Table k -> IO ()
growTable tbl = do
  keys <- getKeys tbl
  vals <- getVals tbl
  let cap   = ML.size keys
  let cap'  = unsafeShiftL cap 1
  let shift = 32 - ctzInt cap'
  keys' <- ML.new @k cap' undefElem
  vals' <- newVals cap'
  setKeys tbl keys'
  setVals tbl vals'

  let go :: Int -> IO ()
      go i | i == cap =
        pure ()
      go i = do
        (!hW, !v) <- splitW64 <$> MP.unsafeRead vals i
        if v == maxBound then
          go (i + 1)
        else do
          k <- ML.unsafeRead keys i
          let ins :: Int -> IO ()
              ins j | j == cap'
                = ins 0
              ins j = do
                (_, v') <- splitW64 <$> MP.unsafeRead vals' j
                if v' == maxBound then do
                  MP.unsafeWrite vals' j (packW64 hW v)
                  ML.unsafeWrite keys' j k
                  go (i + 1)
                else
                  ins (j + 1)
          ins (fromIntegral (unsafeShiftR hW shift))
  go 0

{-# INLINE insertLookup #-}
insertLookup :: forall k a. Hashable k
             => Table k -> k -> IO Word32
             -> (Word32 -> IO a)   -- continue with found value
             -> (Word32 -> IO a)   -- continue after insertion with given new value
             -> IO a
insertLookup tbl k newVal found notfound = do
  sizeRef <- getSizeRef tbl
  size    <- MP.unsafeRead sizeRef 0
  keys    <- getKeys tbl
  vals    <- getVals tbl
  let cap   = ML.size keys
  let hW    = fromIntegral (hash k) :: Word32
  let shift = 32 - ctzInt cap
  let ix    = fromIntegral (unsafeShiftR hW shift) :: Int

  let scan :: Int -> IO a
      scan ix | ix == cap =
        scan 0
      scan ix = do
        (!h', !v) <- splitW64 <$> MP.unsafeRead vals ix
        if v == maxBound then do
          let size' = size + 1
          MP.unsafeWrite sizeRef 0 size'
          v' <- newVal
          MP.unsafeWrite vals ix (packW64 hW v')
          ML.unsafeWrite keys ix k
          when (size' >= unsafeShiftR cap 1) $ growTable tbl
          notfound v'
        else if hW == h' then do
          k' <- ML.unsafeRead keys ix
          if k == k' then do
            found v
          else
            scan (ix + 1)
        else
          scan (ix + 1)
  scan ix

toList :: Table k -> IO [(k, Word32)]
toList tbl = do
  keys <- getKeys tbl
  vals <- getVals tbl
  let cap = ML.size keys
  let go ix acc | ix == cap =
        pure acc
      go ix acc = do
        (_, v) <- splitW64 <$> MP.unsafeRead vals ix
        if v == maxBound then
          go (ix + 1) acc
        else do
          k <- ML.unsafeRead keys ix
          go (ix + 1) ((k, v) : acc)
  go 0 []

-- insertIfNotThere :: Hashable k => Table k -> k -> Word32 -> IO ()
-- insertIfNotThere t k v = insertLookup t k (\_ -> pure ()) (pure v) (pure ())

-- debug :: Table k -> IO (Int, [(Int, Maybe k)], [(Int, Word32, Word32)])
-- debug tbl = do
--   sizeRef <- getSizeRef tbl
--   size    <- MP.unsafeRead sizeRef 0
--   keys    <- getKeys tbl
--   vals    <- getVals tbl
--   keys    <- L.toList <$> ML.freeze keys
--   vals    <- map splitW64 . P.toList <$> MP.freeze vals
--   keys    <- pure $ zipWith3 (\i (_, v) ~k -> (i, k <$ guard (v /= maxBound)))
--                              [0..] vals keys
--   vals    <- pure $ zipWith (\i (a, b) -> (i, a, b)) [0..] vals
--   pure (size, keys, vals)

-- debug' :: Show k => Table k -> IO ()
-- debug' t = do
--   (s, ks, vs) <- debug t
--   putStrLn $ "size: " ++ show s
--   forM_ ks print
--   forM_ vs print

-- test = do
--   t <- new @String
--   forM [0..8] \n -> insertIfNotThere t (show n) 10
--   debug' t
--   print =<< HashConsTable.toList t

--------------------------------------------------------------------------------
