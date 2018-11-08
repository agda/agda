-- New feature by Jesper Cockx in commit be89d4a8b264dd2719cb8c601a2c7f45a95ba220 :
-- disabling the universe check for a data or record type.

-- Andreas, 2018-10-27, re issue #3327: restructured test cases.

module _ where

-- Pragma is naturally attached to definition.

module DataDef where

  data U : Set
  T : U → Set

  {-# NO_UNIVERSE_CHECK #-}
  data U where
    pi : (A : Set)(b : A → U) → U

  T (pi A b) = (x : A) → T (b x)

-- Pragma can also be attached to signature.

module DataSig where

  {-# NO_UNIVERSE_CHECK #-}
  data U : Set
  T : U → Set

  data U where
    pi : (A : Set)(b : A → U) → U

  T (pi A b) = (x : A) → T (b x)

-- Works also for explicit mutual blocks.

module Mutual where

  {-# NO_UNIVERSE_CHECK #-}
  data U : Set where
    pi : (A : Set)(b : A → U) → U

  T : U → Set
  T (pi A b) = (x : A) → T (b x)

-- Records:

module Records where

  {-# NO_UNIVERSE_CHECK #-}
  record R : Set where
    field out : Set

  {-# NO_UNIVERSE_CHECK #-}
  record S : Set

  record S where
    field out : Set
