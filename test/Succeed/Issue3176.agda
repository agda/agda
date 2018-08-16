-- Andreas, 2018-08-14, issue #3176, reported by identicalsnowflake
--
-- Absurd lambdas should be equal.
-- In this case, they were only considered equal during give, but not upon reload.

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
[ V       ] k t = t
[ K i     ] k _ = k i
[ s₁ X s₂ ] k t = [ s₁ ] k t × [ s₂ ] k t

postulate
  ignore : ∀ {t : Set} → t

_<*>_ : ∀ {s : S 0} {t₁ t₂}
  → [ s ] (λ ()) (t₁ → t₂)
  → [ s ] (λ ()) t₁
  → [ s ] (λ ()) t₂
_<*>_ {s₁ X s₂} {t₁} {t₂} (f , _) (x , _) =
  let v : [ s₁ ] (λ ()) t₂
      v = _<*>_ {s = s₁} {t₁ = t₁} {t₂ = t₂} f x
  in
  ignore
_<*>_ f x = ignore

-- Should succeed.
