open import Common.Prelude

infixr 9 _∘_

_∘_ : {A B C : Set} → (B → C) → (A → B) → (A → C)
f ∘ g = λ x → f (g x)

test : Nat → Nat
test = _* 5 ∘ 6 +_ ∘ 2 ∸_
