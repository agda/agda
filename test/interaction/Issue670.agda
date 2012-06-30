-- Andreas, 2012-06-30, case reported by Noam Zeilbereger
module Issue670 where

infix 4 _≡_

data _≡_ {A : Set} (x : A) : A → Set where
  refl : x ≡ x

data Nat : Set where
  zero : Nat
  suc  : Nat → Nat

{-# BUILTIN NATURAL Nat  #-}
{-# BUILTIN SUC     suc  #-}
{-# BUILTIN ZERO    zero #-}

record T : Set where
    field
      x : Nat
      .eq : x ≡ x

foo : T
foo = record { x = 0 ; eq = refl }

bar : T
bar = record { x = 0 ; eq = {!refl!} }
-- give should succeed
