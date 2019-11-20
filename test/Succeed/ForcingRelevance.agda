
open import Agda.Builtin.Nat
open import Agda.Builtin.Equality

data Ix : Set where
  ix : .(i : Nat) (n : Nat) → Ix

data D : Ix → Set where
  mkD : ∀ n → D (ix n n)

data ΣD : Set where
  _,_ : ∀ i → D i → ΣD

foo : ΣD → Nat
foo (i , mkD n) = n

d :  ΣD
d = ix 0 6 , mkD 6

-- Check that we pick the right (the non-irrelevant) `n` when binding
-- the forced argument.
check : foo d ≡ 6
check = refl
