------------------------------------------------------------------------
-- The Agda standard library
--
-- Function setoids and related constructions
------------------------------------------------------------------------

module Function.Equality where

import Function as Fun
open import Level
import Relation.Binary as B
import Relation.Binary.Indexed as I

------------------------------------------------------------------------
-- Functions which preserve equality

record Π {f₁ f₂ t₁ t₂}
         (From : B.Setoid f₁ f₂)
         (To : I.Setoid (B.Setoid.Carrier From) t₁ t₂) :
         Set (f₁ ⊔ f₂ ⊔ t₁ ⊔ t₂) where
  open I using (_=[_]⇒_)
  infixl 5 _⟨$⟩_
  field
    _⟨$⟩_ : (x : B.Setoid.Carrier From) → I.Setoid.Carrier To x
    cong  : B.Setoid._≈_ From =[ _⟨$⟩_ ]⇒ I.Setoid._≈_ To

open Π public

infixr 0 _⟶_

_⟶_ : ∀ {f₁ f₂ t₁ t₂} → B.Setoid f₁ f₂ → B.Setoid t₁ t₂ → Set _
From ⟶ To = Π From (B.Setoid.indexedSetoid To)

-- Identity and composition.

id : ∀ {a₁ a₂} {A : B.Setoid a₁ a₂} → A ⟶ A
id = record { _⟨$⟩_ = Fun.id; cong = Fun.id }

infixr 9 _∘_

_∘_ : ∀ {a₁ a₂} {A : B.Setoid a₁ a₂}
        {b₁ b₂} {B : B.Setoid b₁ b₂}
        {c₁ c₂} {C : B.Setoid c₁ c₂} →
      B ⟶ C → A ⟶ B → A ⟶ C
f ∘ g = record
  { _⟨$⟩_ = Fun._∘_ (_⟨$⟩_ f) (_⟨$⟩_ g)
  ; cong  = Fun._∘_ (cong  f) (cong  g)
  }

-- Constant equality-preserving function.

const : ∀ {a₁ a₂} {A : B.Setoid a₁ a₂}
          {b₁ b₂} {B : B.Setoid b₁ b₂} →
        B.Setoid.Carrier B → A ⟶ B
const {B = B} b = record
  { _⟨$⟩_ = Fun.const b
  ; cong  = Fun.const (B.Setoid.refl B)
  }

------------------------------------------------------------------------
-- Function setoids

-- Dependent.

setoid : ∀ {f₁ f₂ t₁ t₂}
         (From : B.Setoid f₁ f₂) →
         I.Setoid (B.Setoid.Carrier From) t₁ t₂ →
         B.Setoid _ _
setoid From To = record
  { Carrier       = Π From To
  ; _≈_           = λ f g → ∀ {x y} → x ≈₁ y → f ⟨$⟩ x ≈₂ g ⟨$⟩ y
  ; isEquivalence = record
    { refl  = λ {f} → cong f
    ; sym   = λ f∼g x∼y → To.sym (f∼g (From.sym x∼y))
    ; trans = λ f∼g g∼h x∼y → To.trans (f∼g From.refl) (g∼h x∼y)
    }
  }
  where
  open module From = B.Setoid From using () renaming (_≈_ to _≈₁_)
  open module To = I.Setoid To   using () renaming (_≈_ to _≈₂_)

-- Non-dependent.

infixr 0 _⇨_

_⇨_ : ∀ {f₁ f₂ t₁ t₂} → B.Setoid f₁ f₂ → B.Setoid t₁ t₂ → B.Setoid _ _
From ⇨ To = setoid From (B.Setoid.indexedSetoid To)

-- A variant of setoid which uses the propositional equality setoid
-- for the domain, and a more convenient definition of _≈_.

≡-setoid : ∀ {f t₁ t₂} (From : Set f) → I.Setoid From t₁ t₂ → B.Setoid _ _
≡-setoid From To = record
  { Carrier       = (x : From) → Carrier x
  ; _≈_           = λ f g → ∀ x → f x ≈ g x
  ; isEquivalence = record
    { refl  = λ {f} x → refl
    ; sym   = λ f∼g x → sym (f∼g x)
    ; trans = λ f∼g g∼h x → trans (f∼g x) (g∼h x)
    }
  } where open I.Setoid To

-- Parameter swapping function.

flip : ∀ {a₁ a₂} {A : B.Setoid a₁ a₂}
         {b₁ b₂} {B : B.Setoid b₁ b₂}
         {c₁ c₂} {C : B.Setoid c₁ c₂} →
       A ⟶ B ⇨ C → B ⟶ A ⇨ C
flip {B = B} f = record
  { _⟨$⟩_ = λ b → record
    { _⟨$⟩_ = λ a → f ⟨$⟩ a ⟨$⟩ b
    ; cong  = λ a₁≈a₂ → cong f a₁≈a₂ (B.Setoid.refl B) }
  ; cong  = λ b₁≈b₂ a₁≈a₂ → cong f a₁≈a₂ b₁≈b₂
  }
