-- Andreas, 2019-07-15, issue #3901, requested by msuperdock
--
-- Allow function spaces  {A} → B  and  {{A}} → B.

postulate
  A B : Set
  foo : {{A}} → B
  bar : {A} → B

-- Original feature request:

open import Agda.Builtin.Unit using (⊤; tt)

data ⊥ : Set where

data Nat : Set where
  zero : Nat
  suc  : Nat → Nat

_≤_ : Nat → Nat → Set
zero ≤ _      = ⊤
suc m ≤ zero  = ⊥
suc m ≤ suc n = m ≤ n

data SList (bound : Nat) : Set where
  []    : SList bound
  scons : (head : Nat)
        → {head ≤ bound}       -- here: anonymous binding
        → (tail : SList head)
        → SList bound

xs : SList zero
xs = scons zero []
