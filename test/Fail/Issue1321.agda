-- Reported by fredrik.forsberg, Oct 21, 2014
-- The following code gives an internal error

-- "An internal error has occurred. Please report this as a bug.
-- Location of the error: src/full/Agda/TypeChecking/InstanceArguments.hs:269"

-- on Agda head, since "n ≠ zero" is not expanded.

open import Common.Prelude
open import Common.Equality

¬ : (A : Set) → Set
¬ A = {{_ : A}} → ⊥

_≠_ : {A : Set} → (A → A → Set)
x ≠ y = ¬ (x ≡ y)

f : (n : Nat) ⦃ _ : n ≠ zero ⦄ -> Nat
f n = n

g : Nat
g = f (suc zero)
