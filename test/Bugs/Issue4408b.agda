module Issue4408b where

open import Agda.Builtin.Equality
open import Agda.Builtin.Sigma
open import Agda.Primitive

id : ∀ {a} {A : Set a} → A → A
id x = x

_∘_ : ∀ {a b c}
        {A : Set a} {B : A → Set b} {C : {x : A} → B x → Set c} →
      (∀ {x} (y : B x) → C y) → (g : (x : A) → B x) →
      ((x : A) → C (g x))
f ∘ g = λ x → f (g x)

infix 0 _↔_

record _↔_ {f t} (From : Set f) (To : Set t) : Set (f ⊔ t) where
  field
    to               : From → To
    from             : To → From
    right-inverse-of : ∀ x → to (from x) ≡ x
    left-inverse-of  : ∀ x → from (to x) ≡ x

infixr 1 _⊎_

data _⊎_ {a b} (A : Set a) (B : Set b) : Set (a ⊔ b) where
  inj₁ : (x : A) → A ⊎ B
  inj₂ : (y : B) → A ⊎ B

[_,_] : ∀ {a b c} {A : Set a} {B : Set b} {C : A ⊎ B → Set c} →
        ((x : A) → C (inj₁ x)) → ((x : B) → C (inj₂ x)) →
        ((x : A ⊎ B) → C x)
[ f , g ] (inj₁ x) = f x
[ f , g ] (inj₂ y) = g y

Σ-map : ∀ {a b p q}
          {A : Set a} {B : Set b} {P : A → Set p} {Q : B → Set q} →
        (f : A → B) → (∀ {x} → P x → Q (f x)) →
        Σ A P → Σ B Q
Σ-map f g = λ p → (f (fst p) , g (snd p))

∃-⊎-distrib-right :
  ∀ {a b c} {A : Set a} {B : Set b} {C : A ⊎ B → Set c} →
  Σ (A ⊎ B) C ↔ Σ A (C ∘ inj₁) ⊎ Σ B (C ∘ inj₂)
∃-⊎-distrib-right {A = A} {B} {C} = record
  { to               = to
  ; from             = from
  ; right-inverse-of = [ (λ _ → refl) , (λ _ → refl) ]
  ; left-inverse-of  = from∘to
  }
  where
  to : Σ (A ⊎ B) C → Σ A (C ∘ inj₁) ⊎ Σ B (C ∘ inj₂)
  to (inj₁ x , y) = inj₁ (x , y)
  to (inj₂ x , y) = inj₂ (x , y)

  from = [ Σ-map inj₁ id , Σ-map inj₂ id ]

  from∘to : ∀ p → from (to p) ≡ p
  from∘to (inj₁ x , y) = refl
  from∘to (inj₂ x , y) = refl
