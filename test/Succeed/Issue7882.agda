module Issue7882 where

open import Agda.Primitive
open import Agda.Builtin.Equality

variable
  a b c : Level

infixr 1 _⊎_

data _⊎_ (A : Set a) (B : Set b) : Set (a ⊔ b) where
  inj₁ : (x : A) → A ⊎ B
  inj₂ : (y : B) → A ⊎ B

⊎-map₂ : {A B D : Set} → (B → D) → (A ⊎ B → A ⊎ D)
⊎-map₂ g (inj₁ x) = inj₁ x
⊎-map₂ g (inj₂ y) = inj₂ (g y)

record Σ {a b} (A : Set a) (B : A → Set b) : Set (a ⊔ b) where
  constructor _,_
  field
    fst : A
    snd : B fst

open Σ public

infixr 4 _,_

_×_ : ∀ (A : Set a) (B : Set b) → Set (a ⊔ b)
A × B = Σ A λ _ → B

×-map₂ : ∀ {A : Set a} {B : A → Set b} {C : A → Set c} →
        (∀ {x} → B x → C x) → Σ A B → Σ A C
×-map₂ f x = x .fst , f (x .snd)

id : {A : Set} → A → A
id x = x

record Bifunctor (F : Set a → Set b → Set (a ⊔ b)) : Set (lsuc (a ⊔ b)) where
  field
    bimap : ∀ {A A′ : Set a} {B B′ : Set b} → (A → A′) → (B → B′) → F A B → F A′ B′

open Bifunctor ⦃...⦄ public

instance
  Bifunctor-⊎ : Bifunctor {a}{b} _⊎_
  Bifunctor-⊎ .bimap f g (inj₁ x) = inj₁ (f x)
  Bifunctor-⊎ .bimap f g (inj₂ y) = inj₂ (g y)

  Bifunctor-× : Bifunctor {a}{b} _×_
  Bifunctor-× .bimap f g x = f (x .fst) , g (x .snd)

variable
  S : Set
  s s' : S
  Err : Set

module _ (STS : S → S → Set) where
  record Computational Err : Set₀ where
    field
      computeProof : (s : S) → Err ⊎ (Σ S (STS s))
      completeness : (s : S) (s' : S)
        → STS s s' → ⊎-map₂ fst (computeProof s) ≡ inj₂ s'

open Computational ⦃...⦄

data STS* {STS : S → S → Set} : S → S → Set where
  BS-base :
    STS s s' → STS* s s'

module _ {STS : S → S → Set} ⦃ _ : Computational STS Err ⦄ where
  Computational-* : Computational (STS* {STS = STS}) Err
  Computational-* .computeProof s = bimap id (×-map₂ BS-base) (computeProof s) -- fails
  -- Computational-* .computeProof s = bimap ⦃ Bifunctor-⊎ ⦄ id (×-map₂ BS-base) (computeProof s) -- doesn't fail
  Computational-* .completeness s s' (BS-base p)
    with computeProof {STS = STS} s | completeness {STS = STS} _ _ p
  ... | inj₂ x | refl = refl
