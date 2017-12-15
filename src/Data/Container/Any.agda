------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties related to ◇
------------------------------------------------------------------------

module Data.Container.Any where

open import Algebra
open import Data.Container as C
open import Data.Container.Combinator
  using (module Composition) renaming (_∘_ to _⟨∘⟩_)
open import Data.Product as Prod hiding (swap)
open import Data.Product.Relation.Pointwise
import Data.Product.Relation.SigmaPointwise as Σ
open import Data.Sum
open import Function
open import Function.Equality using (_⟨$⟩_)
open import Function.Equivalence using (equivalence)
open import Function.Inverse as Inv using (_↔_; module Inverse)
open import Function.Related as Related using (Related)
open import Function.Related.TypeIsomorphisms
import Relation.Binary.HeterogeneousEquality as H
open import Relation.Binary.PropositionalEquality as P
  using (_≡_; _≗_; refl)

open Related.EquationalReasoning
private
  module ×⊎ {k ℓ} = CommutativeSemiring (×⊎-CommutativeSemiring k ℓ)

-- ◇ can be expressed using _∈_.

↔∈ : ∀ {c} (C : Container c) {X : Set c}
       {P : X → Set c} {xs : ⟦ C ⟧ X} →
     ◇ P xs ↔ (∃ λ x → x ∈ xs × P x)
↔∈ _ {P = P} {xs} = record
  { to         = P.→-to-⟶ to
  ; from       = P.→-to-⟶ from
  ; inverse-of = record
    { left-inverse-of  = λ _ → refl
    ; right-inverse-of = to∘from
    }
  }
  where
  to : ◇ P xs → ∃ λ x → x ∈ xs × P x
  to (p , Px) = (proj₂ xs p , (p , refl) , Px)

  from : (∃ λ x → x ∈ xs × P x) → ◇ P xs
  from (.(proj₂ xs p) , (p , refl) , Px) = (p , Px)

  to∘from : to ∘ from ≗ id
  to∘from (.(proj₂ xs p) , (p , refl) , Px) = refl

-- ◇ is a congruence for bag and set equality and related preorders.

cong : ∀ {k c} {C : Container c}
         {X : Set c} {P₁ P₂ : X → Set c} {xs₁ xs₂ : ⟦ C ⟧ X} →
       (∀ x → Related k (P₁ x) (P₂ x)) → xs₁ ∼[ k ] xs₂ →
       Related k (◇ P₁ xs₁) (◇ P₂ xs₂)
cong {C = C} {P₁ = P₁} {P₂} {xs₁} {xs₂} P₁↔P₂ xs₁≈xs₂ =
  ◇ P₁ xs₁                  ↔⟨ ↔∈ C ⟩
  (∃ λ x → x ∈ xs₁ × P₁ x)  ∼⟨ Σ.cong Inv.id (xs₁≈xs₂ ×-cong P₁↔P₂ _) ⟩
  (∃ λ x → x ∈ xs₂ × P₂ x)  ↔⟨ sym (↔∈ C) ⟩
  ◇ P₂ xs₂                  ∎

-- Nested occurrences of ◇ can sometimes be swapped.

swap : ∀ {c} {C₁ C₂ : Container c} {X Y : Set c} {P : X → Y → Set c}
         {xs : ⟦ C₁ ⟧ X} {ys : ⟦ C₂ ⟧ Y} →
       let ◈ : ∀ {C : Container c} {X} → ⟦ C ⟧ X → (X → Set c) → Set c
           ◈ = λ {_} {_} → flip ◇ in
       ◈ xs (◈ ys ∘ P) ↔ ◈ ys (◈ xs ∘ flip P)
swap {c} {C₁} {C₂} {P = P} {xs} {ys} =
  ◇ (λ x → ◇ (P x) ys) xs                    ↔⟨ ↔∈ C₁ ⟩
  (∃ λ x → x ∈ xs × ◇ (P x) ys)              ↔⟨ Σ.cong Inv.id (λ {x} → Inv.id ⟨ ×⊎.*-cong {ℓ = c} ⟩ ↔∈ C₂ {P = P x}) ⟩
  (∃ λ x → x ∈ xs × ∃ λ y → y ∈ ys × P x y)  ↔⟨ Σ.cong Inv.id (λ {x} → ∃∃↔∃∃ {A = x ∈ xs} (λ _ y → y ∈ ys × P x y)) ⟩
  (∃₂ λ x y → x ∈ xs × y ∈ ys × P x y)       ↔⟨ ∃∃↔∃∃ (λ x y → x ∈ xs × y ∈ ys × P x y) ⟩
  (∃₂ λ y x → x ∈ xs × y ∈ ys × P x y)       ↔⟨ Σ.cong Inv.id (λ {y} → Σ.cong Inv.id (λ {x} →
    (x ∈ xs × y ∈ ys × P x y)                     ↔⟨ sym $ ×⊎.*-assoc _ _ _ ⟩
    ((x ∈ xs × y ∈ ys) × P x y)                   ↔⟨ ×⊎.*-comm _ _ ⟨ ×⊎.*-cong {ℓ = c} ⟩ Inv.id ⟩
    ((y ∈ ys × x ∈ xs) × P x y)                   ↔⟨ ×⊎.*-assoc _ _ _ ⟩
    (y ∈ ys × x ∈ xs × P x y)                     ∎)) ⟩
  (∃₂ λ y x → y ∈ ys × x ∈ xs × P x y)       ↔⟨ Σ.cong Inv.id (λ {y} → ∃∃↔∃∃ {B = y ∈ ys} (λ x _ → x ∈ xs × P x y)) ⟩
  (∃ λ y → y ∈ ys × ∃ λ x → x ∈ xs × P x y)  ↔⟨ Σ.cong Inv.id (λ {y} → Inv.id ⟨ ×⊎.*-cong {ℓ = c} ⟩ sym (↔∈ C₁ {P = flip P y})) ⟩
  (∃ λ y → y ∈ ys × ◇ (flip P y) xs)         ↔⟨ sym (↔∈ C₂) ⟩
  ◇ (λ y → ◇ (flip P y) xs) ys               ∎

-- Nested occurrences of ◇ can sometimes be flattened.

flatten : ∀ {c} {C₁ C₂ : Container c} {X}
          P (xss : ⟦ C₁ ⟧ (⟦ C₂ ⟧ X)) →
          ◇ (◇ P) xss ↔
          ◇ P (Inverse.from (Composition.correct C₁ C₂) ⟨$⟩ xss)
flatten {C₁ = C₁} {C₂} {X} P xss = record
  { to         = P.→-to-⟶ t
  ; from       = P.→-to-⟶ f
  ; inverse-of = record
    { left-inverse-of  = λ _ → refl
    ; right-inverse-of = λ _ → refl
    }
  }
  where
  open Inverse

  t : ◇ (◇ P) xss → ◇ P (from (Composition.correct C₁ C₂) ⟨$⟩ xss)
  t (p₁ , p₂ , p) = ((p₁ , p₂) , p)

  f : ◇ P (from (Composition.correct C₁ C₂) ⟨$⟩ xss) → ◇ (◇ P) xss
  f ((p₁ , p₂) , p) = (p₁ , p₂ , p)

-- Sums commute with ◇ (for a fixed instance of a given container).

◇⊎↔⊎◇ : ∀ {c} {C : Container c} {X : Set c} {xs : ⟦ C ⟧ X}
          {P Q : X → Set c} →
        ◇ (λ x → P x ⊎ Q x) xs ↔ (◇ P xs ⊎ ◇ Q xs)
◇⊎↔⊎◇ {xs = xs} {P} {Q} = record
  { to         = P.→-to-⟶ to
  ; from       = P.→-to-⟶ from
  ; inverse-of = record
    { left-inverse-of  = from∘to
    ; right-inverse-of = [ (λ _ → refl) , (λ _ → refl) ]
    }
  }
  where
  to : ◇ (λ x → P x ⊎ Q x) xs → ◇ P xs ⊎ ◇ Q xs
  to (pos , inj₁ p) = inj₁ (pos , p)
  to (pos , inj₂ q) = inj₂ (pos , q)

  from : ◇ P xs ⊎ ◇ Q xs → ◇ (λ x → P x ⊎ Q x) xs
  from = [ Prod.map id inj₁ , Prod.map id inj₂ ]

  from∘to : from ∘ to ≗ id
  from∘to (pos , inj₁ p) = refl
  from∘to (pos , inj₂ q) = refl

-- Products "commute" with ◇.

×◇↔◇◇× : ∀ {c} {C₁ C₂ : Container c}
           {X Y} {P : X → Set c} {Q : Y → Set c}
           {xs : ⟦ C₁ ⟧ X} {ys : ⟦ C₂ ⟧ Y} →
         ◇ (λ x → ◇ (λ y → P x × Q y) ys) xs ↔ (◇ P xs × ◇ Q ys)
×◇↔◇◇× {C₁ = C₁} {C₂} {P = P} {Q} {xs} {ys} = record
  { to         = P.→-to-⟶ to
  ; from       = P.→-to-⟶ from
  ; inverse-of = record
    { left-inverse-of  = λ _ → refl
    ; right-inverse-of = λ _ → refl
    }
  }
  where
  to : ◇ (λ x → ◇ (λ y → P x × Q y) ys) xs → ◇ P xs × ◇ Q ys
  to (p₁ , p₂ , p , q) = ((p₁ , p) , (p₂ , q))

  from : ◇ P xs × ◇ Q ys → ◇ (λ x → ◇ (λ y → P x × Q y) ys) xs
  from ((p₁ , p) , (p₂ , q)) = (p₁ , p₂ , p , q)

-- map can be absorbed by the predicate.

map↔∘ : ∀ {c} (C : Container c) {X Y : Set c}
        (P : Y → Set c) {xs : ⟦ C ⟧ X} (f : X → Y) →
        ◇ P (C.map f xs) ↔ ◇ (P ∘ f) xs
map↔∘ _ _ _ = Inv.id

-- Membership in a mapped container can be expressed without reference
-- to map.

∈map↔∈×≡ : ∀ {c} (C : Container c) {X Y : Set c} {f : X → Y}
             {xs : ⟦ C ⟧ X} {y} →
           y ∈ C.map f xs ↔ (∃ λ x → x ∈ xs × y ≡ f x)
∈map↔∈×≡ {c} C {f = f} {xs} {y} =
  y ∈ C.map f xs              ↔⟨ map↔∘ C (_≡_ y) f ⟩
  ◇ (λ x → y ≡ f x) xs        ↔⟨ ↔∈ C ⟩
  (∃ λ x → x ∈ xs × y ≡ f x)  ∎

-- map is a congruence for bag and set equality and related preorders.

map-cong : ∀ {k c} {C : Container c} {X Y : Set c}
             {f₁ f₂ : X → Y} {xs₁ xs₂ : ⟦ C ⟧ X} →
           f₁ ≗ f₂ → xs₁ ∼[ k ] xs₂ →
           C.map f₁ xs₁ ∼[ k ] C.map f₂ xs₂
map-cong {c = c} {C} {f₁ = f₁} {f₂} {xs₁} {xs₂} f₁≗f₂ xs₁≈xs₂ {x} =
  x ∈ C.map f₁ xs₁        ↔⟨ map↔∘ C (_≡_ x) f₁ ⟩
  ◇ (λ y → x ≡ f₁ y) xs₁  ∼⟨ cong {xs₁ = xs₁} {xs₂ = xs₂} (Related.↔⇒ ∘ helper) xs₁≈xs₂ ⟩
  ◇ (λ y → x ≡ f₂ y) xs₂  ↔⟨ sym (map↔∘ C (_≡_ x) f₂) ⟩
  x ∈ C.map f₂ xs₂        ∎
  where
  helper : ∀ y → (x ≡ f₁ y) ↔ (x ≡ f₂ y)
  helper y = record
    { to         = P.→-to-⟶ (λ x≡f₁y → P.trans x≡f₁y (        f₁≗f₂ y))
    ; from       = P.→-to-⟶ (λ x≡f₂y → P.trans x≡f₂y (P.sym $ f₁≗f₂ y))
    ; inverse-of = record
      { left-inverse-of  = λ _ → P.≡-irrelevance _ _
      ; right-inverse-of = λ _ → P.≡-irrelevance _ _
      }
    }

-- Uses of linear morphisms can be removed.

remove-linear :
  ∀ {c} {C₁ C₂ : Container c} {X} {xs : ⟦ C₁ ⟧ X}
  (P : X → Set c) (m : C₁ ⊸ C₂) →
  ◇ P (⟪ m ⟫⊸ xs) ↔ ◇ P xs
remove-linear {xs = xs} P m = record
  { to         = P.→-to-⟶ t
  ; from       = P.→-to-⟶ f
  ; inverse-of = record
    { left-inverse-of  = f∘t
    ; right-inverse-of = t∘f
    }
  }
  where
  open Inverse

  t : ◇ P (⟪ m ⟫⊸ xs) → ◇ P xs
  t = Prod.map (_⟨$⟩_ (to (position⊸ m))) id

  f : ◇ P xs → ◇ P (⟪ m ⟫⊸ xs)
  f = Prod.map (_⟨$⟩_ (from (position⊸ m)))
               (P.subst (P ∘ proj₂ xs)
                        (P.sym $ right-inverse-of (position⊸ m) _))

  f∘t : f ∘ t ≗ id
  f∘t (p₂ , p) = H.≅-to-≡ $
    H.cong₂ _,_ (H.≡-to-≅ $ left-inverse-of (position⊸ m) p₂)
                (H.≡-subst-removable
                  (P ∘ proj₂ xs)
                  (P.sym (right-inverse-of (position⊸ m)
                                           (to (position⊸ m) ⟨$⟩ p₂)))
                  p)

  t∘f : t ∘ f ≗ id
  t∘f (p₁ , p) = H.≅-to-≡ $
    H.cong₂ _,_ (H.≡-to-≅ $ right-inverse-of (position⊸ m) p₁)
                (H.≡-subst-removable
                  (P ∘ proj₂ xs)
                  (P.sym (right-inverse-of (position⊸ m) p₁))
                  p)

-- Linear endomorphisms are identity functions if bag equality is
-- used.

linear-identity :
  ∀ {c} {C : Container c} {X} {xs : ⟦ C ⟧ X} (m : C ⊸ C) →
  ⟪ m ⟫⊸ xs ∼[ bag ] xs
linear-identity {xs = xs} m {x} =
  x ∈ ⟪ m ⟫⊸ xs  ↔⟨ remove-linear (_≡_ x) m ⟩
  x ∈        xs  ∎

-- If join can be expressed using a linear morphism (in a certain
-- way), then it can be absorbed by the predicate.

join↔◇ : ∀ {c} {C₁ C₂ C₃ : Container c} {X}
         P (join′ : (C₁ ⟨∘⟩ C₂) ⊸ C₃) (xss : ⟦ C₁ ⟧ (⟦ C₂ ⟧ X)) →
         let join : ∀ {X} → ⟦ C₁ ⟧ (⟦ C₂ ⟧ X) → ⟦ C₃ ⟧ X
             join = λ {_} → ⟪ join′ ⟫⊸ ∘
                    _⟨$⟩_ (Inverse.from (Composition.correct C₁ C₂)) in
         ◇ P (join xss) ↔ ◇ (◇ P) xss
join↔◇ {C₁ = C₁} {C₂} P join xss =
  ◇ P (⟪ join ⟫⊸ xss′)  ↔⟨ remove-linear P join ⟩
  ◇ P            xss′   ↔⟨ sym $ flatten P xss ⟩
  ◇ (◇ P) xss           ∎
  where xss′ = Inverse.from (Composition.correct C₁ C₂) ⟨$⟩ xss
