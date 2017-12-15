------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties related to All
------------------------------------------------------------------------

module Data.List.All.Properties where

open import Data.Bool.Base using (Bool; T)
open import Data.Bool.Properties
open import Data.Empty
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.List.Base
open import Data.List.Any.Membership.Propositional
open import Data.List.All as All using (All; []; _∷_)
open import Data.List.Any using (Any; here; there)
open import Data.Nat using (zero; suc; z≤n; s≤s; _<_)
open import Data.Product as Prod using (_×_; _,_; uncurry; uncurry′)
open import Function
open import Function.Equality using (_⟨$⟩_)
open import Function.Equivalence using (_⇔_; module Equivalence)
open import Function.Inverse using (_↔_)
open import Function.Surjection using (_↠_)
open import Relation.Binary.PropositionalEquality as P using (_≡_)
open import Relation.Nullary
open import Relation.Unary
  using (Decidable; Universal) renaming (_⊆_ to _⋐_)

------------------------------------------------------------------------ Basic properties of All

module _ {a p} {A : Set a} {P : A → Set p} where

  -- When P is universal All P holds
  All-universal : Universal P → ∀ xs → All P xs
  All-universal u [] = []
  All-universal u (x ∷ xs) = u x ∷ All-universal u xs

  All-irrelevance : P.IrrelevantPred P → P.IrrelevantPred (All P)
  All-irrelevance irr []           []           = P.refl
  All-irrelevance irr (px₁ ∷ pxs₁) (px₂ ∷ pxs₂) =
    P.cong₂ _∷_ (irr px₁ px₂) (All-irrelevance irr pxs₁ pxs₂)

------------------------------------------------------------------------
-- Lemmas relating Any, All and negation.

module _ {a p} {A : Set a} {P : A → Set p} where

  ¬Any⇒All¬ : ∀ xs → ¬ Any P xs → All (¬_ ∘ P) xs
  ¬Any⇒All¬ []       ¬p = []
  ¬Any⇒All¬ (x ∷ xs) ¬p = ¬p ∘ here ∷ ¬Any⇒All¬ xs (¬p ∘ there)

  All¬⇒¬Any : ∀ {xs} → All (¬_ ∘ P) xs → ¬ Any P xs
  All¬⇒¬Any []        ()
  All¬⇒¬Any (¬p ∷ _)  (here  p) = ¬p p
  All¬⇒¬Any (_  ∷ ¬p) (there p) = All¬⇒¬Any ¬p p

  ¬All⇒Any¬ : Decidable P → ∀ xs → ¬ All P xs → Any (¬_ ∘ P) xs
  ¬All⇒Any¬ dec []       ¬∀ = ⊥-elim (¬∀ [])
  ¬All⇒Any¬ dec (x ∷ xs) ¬∀ with dec x
  ... | yes p = there (¬All⇒Any¬ dec xs (¬∀ ∘ _∷_ p))
  ... | no ¬p = here ¬p

  Any¬→¬All : ∀ {xs} → Any (¬_ ∘ P) xs → ¬ All P xs
  Any¬→¬All (here  ¬p) = ¬p           ∘ All.head
  Any¬→¬All (there ¬p) = Any¬→¬All ¬p ∘ All.tail

  ¬Any↠All¬ : ∀ {xs} → (¬ Any P xs) ↠ All (¬_ ∘ P) xs
  ¬Any↠All¬ = record
    { to         = P.→-to-⟶ (¬Any⇒All¬ _)
    ; surjective = record
      { from             = P.→-to-⟶ All¬⇒¬Any
      ; right-inverse-of = to∘from
      }
    }
    where

    to∘from : ∀ {xs} (¬p : All (¬_ ∘ P) xs) → ¬Any⇒All¬ xs (All¬⇒¬Any ¬p) ≡ ¬p
    to∘from []         = P.refl
    to∘from (¬p ∷ ¬ps) = P.cong₂ _∷_ P.refl (to∘from ¬ps)

    -- If equality of functions were extensional, then the surjection
    -- could be strengthened to a bijection.

    from∘to : P.Extensionality _ _ →
              ∀ xs → (¬p : ¬ Any P xs) → All¬⇒¬Any (¬Any⇒All¬ xs ¬p) ≡ ¬p
    from∘to ext []       ¬p = ext λ ()
    from∘to ext (x ∷ xs) ¬p = ext λ
      { (here p)  → P.refl
      ; (there p) → P.cong (λ f → f p) $ from∘to ext xs (¬p ∘ there)
      }

  Any¬⇔¬All : ∀ {xs} → Decidable P → Any (¬_ ∘ P) xs ⇔ (¬ All P xs)
  Any¬⇔¬All dec = record
    { to   = P.→-to-⟶ Any¬→¬All
    ; from = P.→-to-⟶ (¬All⇒Any¬ dec _)
    }
    where

    -- If equality of functions were extensional, then the logical
    -- equivalence could be strengthened to a surjection.

    to∘from : P.Extensionality _ _ →
              ∀ {xs} (¬∀ : ¬ All P xs) → Any¬→¬All (¬All⇒Any¬ dec xs ¬∀) ≡ ¬∀
    to∘from ext ¬∀ = ext (⊥-elim ∘ ¬∀)

------------------------------------------------------------------------
-- Lemmas relating All to ⊤

All-all : ∀ {a} {A : Set a} (p : A → Bool) {xs} →
          All (T ∘ p) xs → T (all p xs)
All-all p []         = _
All-all p (px ∷ pxs) = Equivalence.from T-∧ ⟨$⟩ (px , All-all p pxs)

all-All : ∀ {a} {A : Set a} (p : A → Bool) xs →
          T (all p xs) → All (T ∘ p) xs
all-All p []       _     = []
all-All p (x ∷ xs) px∷xs with Equivalence.to (T-∧ {p x}) ⟨$⟩ px∷xs
all-All p (x ∷ xs) px∷xs | (px , pxs) = px ∷ all-All p xs pxs

------------------------------------------------------------------------
-- All is anti-monotone.

anti-mono : ∀ {a p} {A : Set a} {P : A → Set p} {xs ys} →
            xs ⊆ ys → All P ys → All P xs
anti-mono xs⊆ys pys = All.tabulate (All.lookup pys ∘ xs⊆ys)

all-anti-mono : ∀ {a} {A : Set a} (p : A → Bool) {xs ys} →
                xs ⊆ ys → T (all p ys) → T (all p xs)
all-anti-mono p xs⊆ys = All-all p ∘ anti-mono xs⊆ys ∘ all-All p _

------------------------------------------------------------------------
-- Introduction (⁺) and elimination (⁻) rules for various list functions
------------------------------------------------------------------------
-- map

module _{a b} {A : Set a} {B : Set b} where

  All-map : ∀ {p} {P : B → Set p} {f : A → B} {xs} →
            All (P ∘ f) xs → All P (map f xs)
  All-map []       = []
  All-map (p ∷ ps) = p ∷ All-map ps

  map-All : ∀ {p} {P : B → Set p} {f : A → B} {xs} →
            All P (map f xs) → All (P ∘ f) xs
  map-All {xs = []}    []       = []
  map-All {xs = _ ∷ _} (p ∷ ps) = p ∷ map-All ps

  -- A variant of All.map.

  gmap : ∀ {p q} {P : A → Set p} {Q : B → Set q} {f : A → B} →
         P ⋐ Q ∘ f → All P ⋐ All Q ∘ map f
  gmap g = All-map ∘ All.map g

------------------------------------------------------------------------
-- _++_

module _ {a p} {A : Set a} {P : A → Set p} where

  ++⁺ : ∀ {xs ys} → All P xs → All P ys → All P (xs ++ ys)
  ++⁺ []         pys = pys
  ++⁺ (px ∷ pxs) pys = px ∷ ++⁺ pxs pys

  ++⁻ˡ : ∀ xs {ys} → All P (xs ++ ys) → All P xs
  ++⁻ˡ []       p          = []
  ++⁻ˡ (x ∷ xs) (px ∷ pxs) = px ∷ (++⁻ˡ _ pxs)

  ++⁻ʳ : ∀ xs {ys} → All P (xs ++ ys) → All P ys
  ++⁻ʳ []       p          = p
  ++⁻ʳ (x ∷ xs) (px ∷ pxs) = ++⁻ʳ xs pxs

  ++⁻ : ∀ xs {ys} → All P (xs ++ ys) → All P xs × All P ys
  ++⁻ []       p          = [] , p
  ++⁻ (x ∷ xs) (px ∷ pxs) = Prod.map (px ∷_) id (++⁻ _ pxs)

  ++↔ : ∀ {xs ys} → (All P xs × All P ys) ↔ All P (xs ++ ys)
  ++↔ {xs} = record
    { to         = P.→-to-⟶ $ uncurry ++⁺
    ; from       = P.→-to-⟶ $ ++⁻ xs
    ; inverse-of = record
      { left-inverse-of  = ++⁻∘++⁺
      ; right-inverse-of = ++⁺∘++⁻ xs
      }
    }
    where

    ++⁺∘++⁻ : ∀ xs {ys} (p : All P (xs ++ ys)) →
              uncurry′ ++⁺ (++⁻ xs p) ≡ p
    ++⁺∘++⁻ []       p          = P.refl
    ++⁺∘++⁻ (x ∷ xs) (px ∷ pxs) = P.cong (_∷_ px) $ ++⁺∘++⁻ xs pxs

    ++⁻∘++⁺ : ∀ {xs ys} (p : All P xs × All P ys) →
              ++⁻ xs (uncurry ++⁺ p) ≡ p
    ++⁻∘++⁺ ([]       , pys) = P.refl
    ++⁻∘++⁺ (px ∷ pxs , pys) rewrite ++⁻∘++⁺ (pxs , pys) = P.refl

------------------------------------------------------------------------
-- concat

module _ {a p} {A : Set a} {P : A → Set p} where

  concat⁺ : ∀ {xss} → All (All P) xss → All P (concat xss)
  concat⁺ []           = []
  concat⁺ (pxs ∷ pxss) = ++⁺ pxs (concat⁺ pxss)

  concat⁻ : ∀ {xss} → All P (concat xss) → All (All P) xss
  concat⁻ {[]}       []  = []
  concat⁻ {xs ∷ xss} pxs = ++⁻ˡ xs pxs ∷ concat⁻ (++⁻ʳ xs pxs)

------------------------------------------------------------------------
-- take and drop

module _ {a p} {A : Set a} {P : A → Set p} where

  drop⁺ : ∀ {xs} n → All P xs → All P (drop n xs)
  drop⁺ zero    pxs        = pxs
  drop⁺ (suc n) []         = []
  drop⁺ (suc n) (px ∷ pxs) = drop⁺ n pxs

  take⁺ : ∀ {xs} n → All P xs → All P (take n xs)
  take⁺ zero    pxs        = []
  take⁺ (suc n) []         = []
  take⁺ (suc n) (px ∷ pxs) = px ∷ take⁺ n pxs

------------------------------------------------------------------------
-- applyUpTo

module _ {a p} {A : Set a} {P : A → Set p} where

  applyUpTo⁺₁ : ∀ f n → (∀ {i} → i < n → P (f i)) → All P (applyUpTo f n)
  applyUpTo⁺₁ f zero    Pf = []
  applyUpTo⁺₁ f (suc n) Pf = Pf (s≤s z≤n) ∷ applyUpTo⁺₁ (f ∘ suc) n (Pf ∘ s≤s)

  applyUpTo⁺₂ : ∀ f n → (∀ i → P (f i)) → All P (applyUpTo f n)
  applyUpTo⁺₂ f n Pf = applyUpTo⁺₁ f n (λ _ → Pf _)

  applyUpTo⁻ : ∀ f n → All P (applyUpTo f n) → ∀ {i} → i < n → P (f i)
  applyUpTo⁻ f zero    pxs        ()
  applyUpTo⁻ f (suc n) (px ∷ _)   (s≤s z≤n)       = px
  applyUpTo⁻ f (suc n) (_  ∷ pxs) (s≤s (s≤s i<n)) =
    applyUpTo⁻ (f ∘ suc) n pxs (s≤s i<n)

------------------------------------------------------------------------
-- tabulate

module _ {a p} {A : Set a} {P : A → Set p} where

  tabulate⁺ : ∀ {n} {f : Fin n → A} →
              (∀ i → P (f i)) → All P (tabulate f)
  tabulate⁺ {zero}  Pf = []
  tabulate⁺ {suc n} Pf = Pf fzero ∷ tabulate⁺ (Pf ∘ fsuc)

  tabulate⁻ : ∀ {n} {f : Fin n → A} →
              All P (tabulate f) → (∀ i → P (f i))
  tabulate⁻ {zero}  pf       ()
  tabulate⁻ {suc n} (px ∷ _) fzero    = px
  tabulate⁻ {suc n} (_ ∷ pf) (fsuc i) = tabulate⁻ pf i
