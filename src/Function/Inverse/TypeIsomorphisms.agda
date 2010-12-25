------------------------------------------------------------------------
-- Various basic type isomorphisms
------------------------------------------------------------------------

{-# OPTIONS --universe-polymorphism #-}

module Function.Inverse.TypeIsomorphisms where

open import Algebra
import Algebra.FunctionProperties as FP
open import Data.Empty
open import Data.Product as Prod hiding (swap)
open import Data.Sum as Sum
open import Data.Unit
open import Level
open import Function
open import Function.Equality using (_⟨$⟩_)
open import Function.Equivalence
  using (_⇔_; equivalent; module Equivalent)
open import Function.Inverse as Inv
  using (Kind; Isomorphism; _⇿_; module Inverse)
open import Relation.Binary
open import Relation.Binary.Product.Pointwise
open import Relation.Binary.PropositionalEquality as P using (_≡_; _≗_)
open import Relation.Binary.Sum
open import Relation.Nullary

------------------------------------------------------------------------
-- ⊥, ⊤, _×_ and _⊎_ form a commutative semiring

×-CommutativeMonoid : Kind → (ℓ : Level) → CommutativeMonoid _ _
×-CommutativeMonoid k ℓ = record
  { Carrier             = Set ℓ
  ; _≈_                 = Isomorphism k
  ; _∙_                 = _×_
  ; ε                   = Lift ⊤
  ; isCommutativeMonoid = record
    { isSemigroup   = record
      { isEquivalence = Setoid.isEquivalence $
                          Inv.Isomorphism-setoid k ℓ
      ; assoc         = λ A B C → Inv.⇿⇒ $ assoc A B C
      ; ∙-cong        = ×-cong k
      }
    ; identityˡ = λ A → Inv.⇿⇒ $ left-identity A
    ; comm      = λ A B → Inv.⇿⇒ $ comm A B
    }
  }
  where
  open FP _⇿_

  ×-cong : ∀ k {A B C D : Set ℓ} →
           Isomorphism k A B → Isomorphism k C D →
           Isomorphism k (A × C) (B × D)
  ×-cong Inv.equivalent = _×-⇔_
  ×-cong Inv.inverse    = _×-⇿_

  left-identity : LeftIdentity (Lift {ℓ = ℓ} ⊤) _×_
  left-identity _ = record
    { to         = P.→-to-⟶ $ proj₂ {a = ℓ} {b = ℓ}
    ; from       = P.→-to-⟶ {b₁ = ℓ} λ y → _ , y
    ; inverse-of = record
      { left-inverse-of  = λ _ → P.refl
      ; right-inverse-of = λ _ → P.refl
      }
    }

  assoc : Associative _×_
  assoc _ _ _ = record
    { to         = P.→-to-⟶ {a = ℓ} {b₁ = ℓ} λ t → (proj₁ (proj₁ t) , (proj₂ (proj₁ t) , proj₂ t))
    ; from       = P.→-to-⟶ {a = ℓ} {b₁ = ℓ} λ t → ((proj₁ t , proj₁ (proj₂ t)) , proj₂ (proj₂ t))
    ; inverse-of = record
      { left-inverse-of  = λ _ → P.refl
      ; right-inverse-of = λ _ → P.refl
      }
    }

  comm : Commutative _×_
  comm _ _ = record
    { to         = P.→-to-⟶ $ Prod.swap {a = ℓ} {b = ℓ}
    ; from       = P.→-to-⟶ $ Prod.swap {a = ℓ} {b = ℓ}
    ; inverse-of = record
      { left-inverse-of  = λ _ → P.refl
      ; right-inverse-of = λ _ → P.refl
      }
    }

⊎-CommutativeMonoid : Kind → (ℓ : Level) → CommutativeMonoid _ _
⊎-CommutativeMonoid k ℓ = record
  { Carrier             = Set ℓ
  ; _≈_                 = Isomorphism k
  ; _∙_                 = _⊎_
  ; ε                   = Lift ⊥
  ; isCommutativeMonoid = record
    { isSemigroup   = record
      { isEquivalence = Setoid.isEquivalence $
                          Inv.Isomorphism-setoid k ℓ
      ; assoc         = λ A B C → Inv.⇿⇒ $ assoc A B C
      ; ∙-cong        = ⊎-cong k
      }
    ; identityˡ = λ A → Inv.⇿⇒ $ left-identity A
    ; comm      = λ A B → Inv.⇿⇒ $ comm A B
    }
  }
  where
  open FP _⇿_

  ⊎-cong : ∀ k {A B C D : Set ℓ} →
           Isomorphism k A B → Isomorphism k C D →
           Isomorphism k (A ⊎ C) (B ⊎ D)
  ⊎-cong Inv.equivalent = _⊎-⇔_
  ⊎-cong Inv.inverse    = _⊎-⇿_

  left-identity : LeftIdentity (Lift ⊥) (_⊎_ {a = ℓ} {b = ℓ})
  left-identity A = record
    { to         = P.→-to-⟶ to
    ; from       = P.→-to-⟶ from
    ; inverse-of = record
      { right-inverse-of = λ _ → P.refl
      ; left-inverse-of  =
          [ ⊥-elim {Whatever = _ ≡ _} ∘ lower , (λ _ → P.refl) ]
      }
    }
    where
    to : Lift {ℓ = ℓ} ⊥ ⊎ A → A
    to = [ (λ ()) ∘′ lower , id ]

    from : A → Lift {ℓ = ℓ} ⊥ ⊎ A
    from = inj₂

  assoc : Associative _⊎_
  assoc A B C = record
    { to         = P.→-to-⟶ to
    ; from       = P.→-to-⟶ from
    ; inverse-of = record
      { left-inverse-of  = [ [ (λ _ → P.refl) , (λ _ → P.refl) ] , (λ _ → P.refl) ]
      ; right-inverse-of = [ (λ _ → P.refl) , [ (λ _ → P.refl) , (λ _ → P.refl) ] ]
      }
    }
    where
    to : (A ⊎ B) ⊎ C → A ⊎ (B ⊎ C)
    to = [ [ inj₁ , inj₂ ∘ inj₁ ] , inj₂ ∘ inj₂ ]

    from : A ⊎ (B ⊎ C) → (A ⊎ B) ⊎ C
    from = [ inj₁ ∘ inj₁ , [ inj₁ ∘ inj₂ , inj₂ ] ]

  comm : Commutative _⊎_
  comm _ _ = record
    { to         = P.→-to-⟶ swap
    ; from       = P.→-to-⟶ swap
    ; inverse-of = record
      { left-inverse-of  = inv
      ; right-inverse-of = inv
      }
    }
    where
    swap : {A B : Set ℓ} → A ⊎ B → B ⊎ A
    swap = [ inj₂ , inj₁ ]

    inv : ∀ {A B} → swap ∘ swap {A} {B} ≗ id
    inv = [ (λ _ → P.refl) , (λ _ → P.refl) ]

×⊎-CommutativeSemiring : Kind → (ℓ : Level) → CommutativeSemiring _ _
×⊎-CommutativeSemiring k ℓ = record
  { Carrier               = Set ℓ
  ; _≈_                   = Isomorphism k
  ; _+_                   = _⊎_
  ; _*_                   = _×_
  ; 0#                    = Lift ⊥
  ; 1#                    = Lift ⊤
  ; isCommutativeSemiring = record
    { +-isCommutativeMonoid = isCommutativeMonoid $
                                ⊎-CommutativeMonoid k ℓ
    ; *-isCommutativeMonoid = isCommutativeMonoid $
                                ×-CommutativeMonoid k ℓ
    ; distribʳ              = λ A B C → Inv.⇿⇒ $ right-distrib A B C
    ; zeroˡ                 = λ A → Inv.⇿⇒ $ left-zero A
    }
  }
  where
  open CommutativeMonoid
  open FP _⇿_

  left-zero : LeftZero (Lift ⊥) (_×_ {a = ℓ} {b = ℓ})
  left-zero A = record
    { to         = P.→-to-⟶ $ proj₁ {a = ℓ} {b = ℓ}
    ; from       = P.→-to-⟶ (⊥-elim ∘′ lower)
    ; inverse-of = record
      { left-inverse-of  = λ p → ⊥-elim (lower $ proj₁ p)
      ; right-inverse-of = λ x → ⊥-elim (lower x)
      }
    }

  right-distrib : _×_ DistributesOverʳ _⊎_
  right-distrib A B C = record
    { to         = P.→-to-⟶ to
    ; from       = P.→-to-⟶ from
    ; inverse-of = record
      { right-inverse-of = [ (λ _ → P.refl) , (λ _ → P.refl) ]
      ; left-inverse-of  =
          uncurry [ (λ _ _ → P.refl) , (λ _ _ → P.refl) ]
      }
    }
    where
    to : (B ⊎ C) × A → B × A ⊎ C × A
    to = uncurry [ curry inj₁ , curry inj₂ ]

    from : B × A ⊎ C × A → (B ⊎ C) × A
    from = [ Prod.map inj₁ id , Prod.map inj₂ id ]

------------------------------------------------------------------------
-- Some reordering lemmas

ΠΠ⇿ΠΠ : ∀ {a b p} {A : Set a} {B : Set b} (P : A → B → Set p) →
        ((x : A) (y : B) → P x y) ⇿ ((y : B) (x : A) → P x y)
ΠΠ⇿ΠΠ _ = record
  { to         = P.→-to-⟶ λ f x y → f y x
  ; from       = P.→-to-⟶ λ f y x → f x y
  ; inverse-of = record
    { left-inverse-of  = λ _ → P.refl
    ; right-inverse-of = λ _ → P.refl
    }
  }

∃∃⇿∃∃ : ∀ {a b p} {A : Set a} {B : Set b} (P : A → B → Set p) →
        (∃₂ λ x y → P x y) ⇿ (∃₂ λ y x → P x y)
∃∃⇿∃∃ {a} {b} {p} _ = record
  { to         = P.→-to-⟶ {a = ℓ} λ p → (proj₁ (proj₂ p) , proj₁ p , proj₂ (proj₂ p))
  ; from       = P.→-to-⟶ {a = ℓ} λ p → (proj₁ (proj₂ p) , proj₁ p , proj₂ (proj₂ p))
  ; inverse-of = record
    { left-inverse-of  = λ _ → P.refl
    ; right-inverse-of = λ _ → P.refl
    }
  } where ℓ = p ⊔ (b ⊔ a)

------------------------------------------------------------------------
-- Implicit and explicit function spaces are isomorphic

Π⇿Π : ∀ {a b} {A : Set a} {B : A → Set b} →
      ((x : A) → B x) ⇿ ({x : A} → B x)
Π⇿Π = record
  { to         = P.→-to-⟶ λ f {x} → f x
  ; from       = P.→-to-⟶ λ f x → f {x}
  ; inverse-of = record
    { left-inverse-of  = λ _ → P.refl
    ; right-inverse-of = λ _ → P.refl
    }
  }

------------------------------------------------------------------------
-- _→_ preserves isomorphisms

_→-cong-⇔_ :
  ∀ {a b c d} {A : Set a} {B : Set b} {C : Set c} {D : Set d} →
  A ⇔ B → C ⇔ D → (A → C) ⇔ (B → D)
A⇔B →-cong-⇔ C⇔D = record
  { to   = P.→-to-⟶ λ f x →
             Equivalent.to   C⇔D ⟨$⟩ f (Equivalent.from A⇔B ⟨$⟩ x)
  ; from = P.→-to-⟶ λ f x →
             Equivalent.from C⇔D ⟨$⟩ f (Equivalent.to   A⇔B ⟨$⟩ x)
  }

→-cong :
  ∀ {a b c d} →
  P.Extensionality a c → P.Extensionality b d →
  ∀ {k} {A : Set a} {B : Set b} {C : Set c} {D : Set d} →
  Isomorphism k A B → Isomorphism k C D → Isomorphism k (A → C) (B → D)
→-cong extAC extBD {Inv.equivalent} A⇔B C⇔D = A⇔B →-cong-⇔ C⇔D
→-cong extAC extBD {Inv.inverse}    A⇿B C⇿D = record
  { to         = Equivalent.to   A→C⇔B→D
  ; from       = Equivalent.from A→C⇔B→D
  ; inverse-of = record
    { left-inverse-of  = λ f → extAC λ x → begin
        Inverse.from C⇿D ⟨$⟩ (Inverse.to C⇿D ⟨$⟩
          f (Inverse.from A⇿B ⟨$⟩ (Inverse.to A⇿B ⟨$⟩ x)))  ≡⟨ Inverse.left-inverse-of C⇿D _ ⟩
        f (Inverse.from A⇿B ⟨$⟩ (Inverse.to A⇿B ⟨$⟩ x))     ≡⟨ P.cong f $ Inverse.left-inverse-of A⇿B x ⟩
        f x                                                 ∎
    ; right-inverse-of = λ f → extBD λ x → begin
        Inverse.to C⇿D ⟨$⟩ (Inverse.from C⇿D ⟨$⟩
          f (Inverse.to A⇿B ⟨$⟩ (Inverse.from A⇿B ⟨$⟩ x)))  ≡⟨ Inverse.right-inverse-of C⇿D _ ⟩
        f (Inverse.to A⇿B ⟨$⟩ (Inverse.from A⇿B ⟨$⟩ x))     ≡⟨ P.cong f $ Inverse.right-inverse-of A⇿B x ⟩
        f x                                                 ∎
    }
  }
  where
  open P.≡-Reasoning
  A→C⇔B→D = Inv.⇿⇒ A⇿B →-cong-⇔ Inv.⇿⇒ C⇿D

------------------------------------------------------------------------
-- ¬_ preserves isomorphisms

¬-cong-⇔ : ∀ {a b} {A : Set a} {B : Set b} →
           A ⇔ B → (¬ A) ⇔ (¬ B)
¬-cong-⇔ A⇔B = A⇔B →-cong-⇔ (⊥ ∎)
  where open Inv.EquationalReasoning

¬-cong : ∀ {a b} →
         P.Extensionality a zero → P.Extensionality b zero →
         ∀ {k} {A : Set a} {B : Set b} →
         Isomorphism k A B → Isomorphism k (¬ A) (¬ B)
¬-cong extA extB A≈B = →-cong extA extB A≈B (⊥ ∎)
  where open Inv.EquationalReasoning

------------------------------------------------------------------------
-- _⇔_ preserves _⇔_

-- The type of the following proof is a bit more general.

Isomorphism-cong :
  ∀ {k a b c d} {A : Set a} {B : Set b} {C : Set c} {D : Set d} →
  Isomorphism k A B → Isomorphism k C D →
  Isomorphism k A C ⇔ Isomorphism k B D
Isomorphism-cong {A = A} {B} {C} {D} A≈B C≈D =
  equivalent (λ A≈C → B  ≈⟨ sym A≈B ⟩
                      A  ≈⟨ A≈C ⟩
                      C  ≈⟨ C≈D ⟩
                      D  ∎)
             (λ B≈D → A  ≈⟨ A≈B ⟩
                      B  ≈⟨ B≈D ⟩
                      D  ≈⟨ sym C≈D ⟩
                      C  ∎)
  where open Inv.EquationalReasoning
