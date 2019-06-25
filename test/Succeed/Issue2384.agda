{-# OPTIONS --show-implicit #-}
-- {-# OPTIONS -v tc.meta.assign:25 #-}

open import Agda.Builtin.Nat renaming (Nat to ℕ)
open import Agda.Builtin.Equality

postulate
  funext : {X : Set} {Y : X → Set} {f g : (x : X) → Y x} → (∀ x → f x ≡ g x) → f ≡ g

_::_ : {X : ℕ → Set} → X 0 → ((n : ℕ) → X (suc n)) → ((n : ℕ) → X n)
(x :: α) 0 = x
(x :: α) (suc n) = α n

hd : {X : ℕ → Set} → ((n : ℕ) → X n) → X 0
hd α = α 0

tl : {X : ℕ → Set} → ((n : ℕ) → X n) → ((n : ℕ) → X (suc n))
tl α n = α(suc n)

-- Needed to add the implicit arguments for funext in Agda 2.5.2:


hd-tl-eta : (X : ℕ → Set) {α : (n : ℕ) → X n} → (hd α :: tl α) ≡ α
hd-tl-eta X {α} = funext {Y = _} (lemma {_})
 where
  lemma : ∀ {α : _} → ∀ i → _::_ {_} (hd α) (tl α) i ≡ α i
  lemma 0 = refl
  lemma (suc i) = refl
