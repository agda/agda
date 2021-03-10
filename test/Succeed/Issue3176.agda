-- Andreas, 2018-08-14, issue #3176, reported by identicalsnowflake
--
-- Absurd lambdas should be equal.
-- In this case, they were only considered equal during give, but not upon reload.

-- {-# OPTIONS -v tc.meta.occurs:35 #-}

open import Agda.Builtin.Nat renaming (Nat to ℕ)
open import Agda.Builtin.Equality

record Σ (A : Set) (B : A → Set) : Set where
  constructor _,_
  field
    proj₁ : A
    proj₂ : B proj₁

open Σ public

∃ : ∀ {A : Set} → (A → Set) → Set
∃ = Σ _

_×_ : ∀ _ _ → _
_×_ a b = ∃ λ (_ : a) → b

record Fin (n : ℕ) : Set where
  field
    m : ℕ
    .p : ∃ λ k → (ℕ.suc k + m) ≡ n

module _ (n : ℕ) where

  data S : Set where
    V : S
    K : Fin n → S
    _X_ : S → S → S

[_] : ∀ {n} → S n → (Fin n → Set) → Set → Set
[ V       ] k A = A
[ K i     ] k _ = k i
[ s₁ X s₂ ] k A = [ s₁ ] k A × [ s₂ ] k A

postulate
  ANY : ∀ {A : Set} → A

_<*>_ : ∀ {s : S 0} {A₁ A₂}
  → [ s ] (λ ()) (A₁ → A₂)
  → [ s ] (λ ()) A₁
  → [ s ] (λ ()) A₂
_<*>_ {s₁ X s₂} {A₁} {A₂} (f , _) (x , _) =
  let v : [ s₁ ] (λ ()) A₂
      v = _<*>_ {s = s₁} {A₁ = A₁} {A₂ = A₂} f x
  in
  ANY -- {A = [ s₁ ] (λ ()) A₂ × [ s₂ ] (λ ()) A₂}
_<*>_ {s = s} f x = ANY -- {A = [ s ] (λ ()) _ }

-- Should succeed.
