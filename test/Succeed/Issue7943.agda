-- Andreas, 2025-06-14, issue #7943 reported and test by tizmd
-- Definitions in erased where modules should not show up in compiled code.

{-# OPTIONS --no-main #-}
{-# OPTIONS --erasure #-}

open import Agda.Builtin.Bool
open import Agda.Builtin.Nat renaming (Nat to ℕ)

record _×₀_ (A : Set) (B : Set) : Set where
  field
    fst : A
    @0 snd : B

open _×₀_

@0 u : ℕ → Bool
u n = n < 10

f :  ℕ → ℕ ×₀ Bool
f n .fst = n
f n .snd = p
  where
    p : Bool -- WAS: remains in the compiled code and causes a compile-time error as missing `u`
    p = u n

-- Compilation should succeed.
