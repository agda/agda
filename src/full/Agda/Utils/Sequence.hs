{-# LANGUAGE MagicHash #-}

{-|
More efficient implementations of some common functions for Data.Sequence.

The problem in the library, in short: since finger trees are given by a nested ADT, well-typed
recursive functions must be polymorphic recursive. But that means a) inlined higher-order function
arguments are impossible b) we must allocate nested closures as we descend into the tree. This is
probably the reason why Data.Sequence is so embarrassingly slow (even though the data structure
itself is quite cool).

In this module, we instead keep track of the nesting depth with a plain 'Int'. Using dependent
types, it would be possible to give a well-typed implementation in this fashion, where we'd iterate
node types on the depth number. Here in Haskell we just unsafeCoerce values based on the depth
number. The upshot is that we don't allocate extra closures, use no polymorphic recursion and we can
inline function arguments.
-}

module Agda.Utils.Sequence where

import Agda.Utils.Function (($$!))
import Data.Sequence
import Data.Sequence.Internal
import GHC.Exts (unsafeCoerce#, Any)

{-# INLINE map' #-}
-- | Strict map.
map' :: forall a b. (a -> b) -> Seq a -> Seq b
map' f = \(Seq as) -> unsafeCoerce# (go 0 (unsafeCoerce# as)) where

  goDigitNodeD :: Int -> Digit Any -> Digit Any
  goDigitNodeD !d = \case
    One a        -> One    $! goNodeD d a
    Two a b      -> Two   $$! goNodeD d a $$! goNodeD d b
    Three a b c  -> Three $$! goNodeD d a $$! goNodeD d b $$! goNodeD d c
    Four a b c x -> Four  $$! goNodeD d a $$! goNodeD d b $$! goNodeD d c $$! goNodeD d x

  goNodeD :: Int -> Any -> Any
  goNodeD d x = case d of
    0 -> unsafeCoerce# (f (unsafeCoerce# x))
    d -> let d' = d - 1 in case unsafeCoerce# x :: Node Any of
      Node2 n a b   -> unsafeCoerce# (Node2 n $$! goNodeD d' a $$! goNodeD d' b)
      Node3 n a b c -> unsafeCoerce# (Node3 n $$! goNodeD d' a $$! goNodeD d' b $$! goNodeD d' c)

  go :: Int -> FingerTree Any -> FingerTree Any
  go !d = \case
    EmptyT         -> EmptyT
    Single a       -> Single $! goNodeD d a
    Deep n ls t rs ->
      Deep n $$! goDigitNodeD d ls
             $$! unsafeCoerce# (go (d + 1) (unsafeCoerce# t))
             $$! goDigitNodeD d rs

-- | Strict left fold, faster than the library version.
{-# INLINE foldl' #-}
foldl' :: forall a b. (b -> a -> b) -> b -> Seq a -> b
foldl' f b = \(Seq as) -> go 0 (unsafeCoerce# as) b where

  goDigitNodeD :: Int -> Digit Any -> b -> b
  goDigitNodeD !d x !acc = case x of
    One a        -> goNodeD d a acc
    Two a b      -> goNodeD d b $! goNodeD d a acc
    Three a b c  -> goNodeD d c $! goNodeD d b $! goNodeD d a acc
    Four a b c x -> goNodeD d x $! goNodeD d c $! goNodeD d b $! goNodeD d a acc

  goNodeD :: Int -> Any -> b -> b
  goNodeD d x !acc = case d of
    0 -> unsafeCoerce# (f acc (unsafeCoerce# x))
    d -> let d' = d - 1 in case unsafeCoerce# x :: Node Any of
      Node2 n a b   -> goNodeD d' b $! goNodeD d' a acc
      Node3 n a b c -> goNodeD d' c $! goNodeD d' b $! goNodeD d' a acc

  go :: Int -> FingerTree Any -> b -> b
  go !d t !acc = case t of
    EmptyT         -> acc
    Single a       -> goNodeD d a acc
    Deep n ls t rs -> goDigitNodeD d rs $! go (d + 1) (unsafeCoerce# t) $! goDigitNodeD d ls acc

-- | Strict right fold, faster than the library version.
{-# INLINE foldr' #-}
foldr' :: forall a b. (a -> b -> b) -> b -> Seq a -> b
foldr' f b = \(Seq as) -> go 0 (unsafeCoerce# as) b where

  goDigitNodeD :: Int -> Digit Any -> b -> b
  goDigitNodeD !d x !acc = case x of
    One a        -> goNodeD d a acc
    Two a b      -> goNodeD d a $! goNodeD d b acc
    Three a b c  -> goNodeD d a $! goNodeD d b $! goNodeD d c acc
    Four a b c x -> goNodeD d a $! goNodeD d b $! goNodeD d c $! goNodeD d x acc

  goNodeD :: Int -> Any -> b -> b
  goNodeD d x !acc = case d of
    0 -> unsafeCoerce# (f (unsafeCoerce# x) acc)
    d -> let d' = d - 1 in case unsafeCoerce# x :: Node Any of
      Node2 n a b   -> goNodeD d' a $! goNodeD d' b acc
      Node3 n a b c -> goNodeD d' a $! goNodeD d' b $! goNodeD d' c acc

  go :: Int -> FingerTree Any -> b -> b
  go !d t !acc = case t of
    EmptyT         -> acc
    Single a       -> goNodeD d a acc
    Deep n ls t rs -> goDigitNodeD d ls $! go (d + 1) (unsafeCoerce# t) $! goDigitNodeD d rs acc

-- | Lazy right fold, faster than the library version.
{-# INLINE foldr #-}
foldr :: forall a b. (a -> b -> b) -> b -> Seq a -> b
foldr f b = \(Seq as) -> go 0 (unsafeCoerce# as) b where

  goDigitNodeD :: Int -> Digit Any -> b -> b
  goDigitNodeD !d x acc = case x of
    One a        -> goNodeD d a acc
    Two a b      -> goNodeD d a $ goNodeD d b acc
    Three a b c  -> goNodeD d a $ goNodeD d b $ goNodeD d c acc
    Four a b c x -> goNodeD d a $ goNodeD d b $ goNodeD d c $ goNodeD d x acc

  goNodeD :: Int -> Any -> b -> b
  goNodeD d x acc = case d of
    0 -> unsafeCoerce# (f (unsafeCoerce# x) acc)
    d -> let d' = d - 1 in case unsafeCoerce# x :: Node Any of
      Node2 n a b   -> goNodeD d' a $ goNodeD d' b acc
      Node3 n a b c -> goNodeD d' a $ goNodeD d' b $ goNodeD d' c acc

  go :: Int -> FingerTree Any -> b -> b
  go !d t acc = case t of
    EmptyT         -> acc
    Single a       -> goNodeD d a acc
    Deep n ls t rs -> let !d' = d + 1 in goDigitNodeD d ls $ go d' (unsafeCoerce# t) $ goDigitNodeD d rs acc

-- | Convert to lazy list.
toList :: Seq a -> [a]
toList = Agda.Utils.Sequence.foldr (:) []

-- | Convert to strict list.
toList' :: Seq a -> [a]
toList' = foldr' (:) []
