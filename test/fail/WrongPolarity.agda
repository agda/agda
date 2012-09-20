-- Andreas, 2012-02-13: polarity info must be correct

{-# OPTIONS --sized-types --show-implicit #-}
-- {-# OPTIONS -v tc.size.solve:20 -v tc.conv.size:20 #-}
-- {-# OPTIONS -v tc.polarity.set:10 -v tc.conv.term.shortcut:20 #-}
module WrongPolarity where

open import Common.Size

data ⊥ : Set where

data Sink (A : Set) : Set where
  sink : (A → ⊥) → Sink A

postulate
  dump : {A : Set} → A → Sink A

-- A sized type
data Nat : {size : Size} → Set where
  zero : {size : Size} → Nat {↑ size}
  suc  : {size : Size} → Nat {size} → Nat {↑ size}

dumpNat : {i : Size} → Nat {i} → Sink (Nat {i})
dumpNat zero        = dump zero
dumpNat (suc {i} n) = dumpNat {i} n
-- should fail!
-- ↑ i !=< i of type Size
-- when checking that the expression dumpNat n has type Sink Nat
