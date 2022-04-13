open import Agda.Builtin.Equality

cong : ∀{a b} {A : Set a} {B : Set b} (f : A → B) {x y : A} (eq : x ≡ y) → f x ≡ f y
cong f refl = refl

record Category : Set₂ where
  field
    Ob  : Set₁
    _⇒_ : Ob → Ob → Set
    _∘_ : ∀ {O P Q} → P ⇒ Q → O ⇒ P → O ⇒ Q

  -- Moving this out of the record fixes the problem.
  idem : {X : Ob} → X ⇒ X → Set₁
  idem {X} f = f ∘ f ≡ f → Set

Sets : Category
Sets = record
    { Ob = Set
    ; _⇒_ = {!!}
    ; _∘_ = λ f g x → f (g x)
    }
open Category Sets

postulate
  Y : Ob
  f : Y ⇒ Y

idem-f : idem {X = _} f  -- Solving the _ fixes the problem
idem-f ff≡f
  with ffx≡fx ← cong {!!} ff≡f
  = Y
