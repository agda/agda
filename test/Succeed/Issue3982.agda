-- Reported by Nils Anders Danielsson in Issue #3960.

open import Agda.Builtin.Unit
open import Agda.Primitive

id : ∀ {a} (A : Set a) → A → A
id _ a = a

apply : ∀ {a b} {A : Set a} {B : Set b} → A → (A → B) → B
apply = λ x f → f x

postulate
  P : ∀ {a} {A : Set a} → A → A → Set a

Q : ∀ {ℓ} → Set ℓ → Set ℓ
Q A = {x y : A} → P x y

postulate
  F : ∀ {a b} → Set a → Set b → Set (a ⊔ b)
  f : ∀ {a b} {A : Set a} {B : Set b} → Q A → Q (F A B)

g : ∀ {a} (A : Set a) → Q A → ⊤
g A q = apply (λ {_ _} → f q) (id (Q (F A A) → ⊤) _)
