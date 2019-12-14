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

-- The previous error message was:
--
-- Cannot instantiate the metavariable _47 to solution
-- piSort _49 (λ z → Set (a ⊔ _b_54 (A = A) (q = q)))
-- since it contains the variable a
-- which is not in scope of the metavariable or irrelevant in the metavariable but relevant in the solution
-- when checking that the expression λ {_} → f q has type
-- {_ = z : _50} → P (_x_59 (A = A) (q = q)) (_y_60 (A = A) (q = q))
