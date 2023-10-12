
{-# LANGUAGE
  UnboxedTuples, TypeOperators, MagicHash, CPP, RankNTypes, TypeApplications,
  DataKinds, ScopedTypeVariables, AllowAmbiguousTypes, KindSignatures, TypeFamilies #-}

module Agda.Utils.PrimData.Unlifted where

{-| Class for types that can be represented as elements of TYPE 'UnliftedRep.
    NOTE: this module is unsound to use in FFI:

    https://gitlab.haskell.org/ghc/ghc/issues/16650

    Do not pass any data to FFI which contains some unlifted value coerced to a
    different unlifted type!
-}

import Data.Kind
import GHC.Exts

#if MIN_VERSION_base(4,16,0)
#else
type UnliftedType = TYPE 'UnliftedRep
#endif

writeUnlifted# ::
   forall (a :: UnliftedType) s. MutableArrayArray# s -> Int# -> a -> State# s -> State# s
writeUnlifted# marr i a s = writeArrayArrayArray# marr i (unsafeCoerce# a) s
{-# INLINE writeUnlifted# #-}

readUnlifted# :: forall (a :: UnliftedType) s.
         MutableArrayArray# s -> Int# -> State# s -> (# State# s, a #)
readUnlifted# marr i s = unsafeCoerce# (readArrayArrayArray# marr i s)
{-# INLINE readUnlifted# #-}

indexUnlifted# :: forall (a :: UnliftedType). ArrayArray# -> Int# -> a
indexUnlifted# arr i = unsafeCoerce# (indexArrayArrayArray# arr i)
{-# INLINE indexUnlifted# #-}

setUnlifted# ::
  forall (a :: UnliftedType) s. MutableArrayArray# s -> a -> State# s -> State# s
setUnlifted# marr a s =
  let go :: MutableArrayArray# s -> a -> State# s -> Int# -> Int# -> State# s
      go marr a s l i = case i ==# l of
        1# -> s
        _  -> case writeUnlifted# marr i a s of s -> go marr a s l (i +# 1#)
  in go marr a s (sizeofMutableArrayArray# marr) 0#
{-# INLINE setUnlifted# #-}

newUnlifted# :: forall (a :: UnliftedType) s. Int# -> a -> State# s -> (# State# s, MutableArrayArray# s #)
newUnlifted# i a s = case newArrayArray# i s of
  (# s, marr #) -> case setUnlifted# marr a s of
    s -> (# s, marr #)
{-# INLINE newUnlifted# #-}

class Unlifted (a :: Type) where
  type Rep a  :: UnliftedType
  to#         :: a -> Rep a
  from#       :: Rep a -> a
  defaultElem :: a
