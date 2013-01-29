------------------------------------------------------------------------
-- The Agda standard library
--
-- Surjections
------------------------------------------------------------------------

module Function.Surjection where

open import Level
open import Function.Equality as F
  using (_⟶_) renaming (_∘_ to _⟪∘⟫_)
open import Function.Equivalence using (Equivalence)
open import Function.Injection           hiding (id; _∘_)
open import Function.LeftInverse as Left hiding (id; _∘_)
open import Data.Product
open import Relation.Binary
import Relation.Binary.PropositionalEquality as P

-- Surjective functions.

record Surjective {f₁ f₂ t₁ t₂}
                  {From : Setoid f₁ f₂} {To : Setoid t₁ t₂}
                  (to : From ⟶ To) :
                  Set (f₁ ⊔ f₂ ⊔ t₁ ⊔ t₂) where
  field
    from             : To ⟶ From
    right-inverse-of : from RightInverseOf to

-- The set of all surjections from one setoid to another.

record Surjection {f₁ f₂ t₁ t₂}
                  (From : Setoid f₁ f₂) (To : Setoid t₁ t₂) :
                  Set (f₁ ⊔ f₂ ⊔ t₁ ⊔ t₂) where
  field
    to         : From ⟶ To
    surjective : Surjective to

  open Surjective surjective public

  right-inverse : RightInverse From To
  right-inverse = record
    { to              = from
    ; from            = to
    ; left-inverse-of = right-inverse-of
    }

  open LeftInverse right-inverse public
    using () renaming (to-from to from-to)

  injective : Injective from
  injective = LeftInverse.injective right-inverse

  injection : Injection To From
  injection = LeftInverse.injection right-inverse

  equivalence : Equivalence From To
  equivalence = record
    { to   = to
    ; from = from
    }

-- Right inverses can be turned into surjections.

fromRightInverse :
  ∀ {f₁ f₂ t₁ t₂} {From : Setoid f₁ f₂} {To : Setoid t₁ t₂} →
  RightInverse From To → Surjection From To
fromRightInverse r = record
  { to         = from
  ; surjective = record
    { from             = to
    ; right-inverse-of = left-inverse-of
    }
  } where open LeftInverse r

-- The set of all surjections from one set to another.

infix 3 _↠_

_↠_ : ∀ {f t} → Set f → Set t → Set _
From ↠ To = Surjection (P.setoid From) (P.setoid To)

-- Identity and composition.

id : ∀ {s₁ s₂} {S : Setoid s₁ s₂} → Surjection S S
id {S = S} = record
  { to         = F.id
  ; surjective = record
    { from             = LeftInverse.to              id′
    ; right-inverse-of = LeftInverse.left-inverse-of id′
    }
  } where id′ = Left.id {S = S}

infixr 9 _∘_

_∘_ : ∀ {f₁ f₂ m₁ m₂ t₁ t₂}
        {F : Setoid f₁ f₂} {M : Setoid m₁ m₂} {T : Setoid t₁ t₂} →
      Surjection M T → Surjection F M → Surjection F T
f ∘ g = record
  { to         = to f ⟪∘⟫ to g
  ; surjective = record
    { from             = LeftInverse.to              g∘f
    ; right-inverse-of = LeftInverse.left-inverse-of g∘f
    }
  }
  where
  open Surjection
  g∘f = Left._∘_ (right-inverse g) (right-inverse f)
