module Issue8867 where

open import Agda.Primitive

postulate
  I : Set
  C : {o : I → Level} → ((i : I) → Set (o i)) → Set

instance postulate
  d : ∀ {m : I → Level} → C (λ i → Set (m i))

it : ∀ {a} {A : Set a} ⦃ _ : A ⦄ → A
it ⦃ x ⦄ = x

test : ∀ {o : I → Level} (F : (i : I) → Set (o i)) ⦃ _ : C F ⦄ → C F
test F = it
