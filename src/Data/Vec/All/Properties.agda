------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties related to All
------------------------------------------------------------------------

module Data.Vec.All.Properties where

open import Data.Vec as Vec using (Vec; []; _∷_; zip; concat; _++_)
open import Data.Vec.Properties using (map-id; lookup-zip)
open import Data.Product as Prod using (_×_; _,_; uncurry; uncurry′)
open import Data.Vec.All as All using (All; All₂; []; _∷_)
open import Function
open import Function.Inverse using (_↔_)
open import Relation.Unary using (Pred) renaming (_⊆_ to _⋐_)
open import Relation.Binary using (REL; Trans)
open import Relation.Binary.PropositionalEquality as P using (_≡_)

-- If P is an irrelevant predicate then All P is also irrelevant

All-irrelevance : ∀ {a p} {A : Set a} {P : Pred A p} →
                  P.IrrelevantPred P →
                  ∀ {n} → P.IrrelevantPred (All P {n})
All-irrelevance irr []           []             = P.refl
All-irrelevance irr (px₁ ∷ pxs₁) (px₂ ∷ pxs₂) =
  P.cong₂ _∷_ (irr px₁ px₂) (All-irrelevance irr pxs₁ pxs₂)

-- Functions can be shifted between the predicate and the vector.

All-map : ∀ {a b p} {A : Set a} {B : Set b} {P : B → Set p}
            {f : A → B} {k} {xs : Vec A k} →
          All (P ∘ f) xs → All P (Vec.map f xs)
All-map []         = []
All-map (px ∷ pxs) = px ∷ All-map pxs

map-All : ∀ {a b p} {A : Set a} {B : Set b} {P : B → Set p}
            {f : A → B} {k} {xs : Vec A k} →
          All P (Vec.map f xs) → All (P ∘ f) xs
map-All {xs = []}    []       = []
map-All {xs = _ ∷ _} (px ∷ pxs) = px ∷ map-All pxs

-- A variant of All.map.

gmap : ∀ {a b p q}
         {A : Set a} {B : Set b} {P : A → Set p} {Q : B → Set q}
         {f : A → B} {k} →
       P ⋐ Q ∘ f → All P {k} ⋐ All Q {k} ∘ Vec.map f
gmap g = All-map ∘ All.map g

------------------------------------------------------------------------
-- All and _++_

module _ {a n p} {A : Set a} {P : A → Set p} where

  All-++⁺ : ∀ {m} {xs : Vec A m} {ys : Vec A n} →
            All P xs → All P ys → All P (xs ++ ys)
  All-++⁺ []         pys = pys
  All-++⁺ (px ∷ pxs) pys = px ∷ All-++⁺ pxs pys

  All-++ˡ⁻ : ∀ {m} (xs : Vec A m) {ys : Vec A n} →
          All P (xs ++ ys) → All P xs
  All-++ˡ⁻ []       _          = []
  All-++ˡ⁻ (x ∷ xs) (px ∷ pxs) = px ∷ All-++ˡ⁻ xs pxs

  All-++ʳ⁻ : ∀ {m} (xs : Vec A m) {ys : Vec A n} →
          All P (xs ++ ys) → All P ys
  All-++ʳ⁻ []       pys        = pys
  All-++ʳ⁻ (x ∷ xs) (px ∷ pxs) = All-++ʳ⁻ xs pxs

  All-++⁻ : ∀ {m} (xs : Vec A m) {ys : Vec A n} →
        All P (xs ++ ys) → All P xs × All P ys
  All-++⁻ []       p          = [] , p
  All-++⁻ (x ∷ xs) (px ∷ pxs) = Prod.map (px ∷_) id (All-++⁻ _ pxs)

  All-++⁺∘++⁻ : ∀ {m} (xs : Vec A m) {ys : Vec A n} →
                (p : All P (xs ++ ys)) →
                uncurry′ All-++⁺ (All-++⁻ xs p) ≡ p
  All-++⁺∘++⁻ []       p          = P.refl
  All-++⁺∘++⁻ (x ∷ xs) (px ∷ pxs) = P.cong (px ∷_) (All-++⁺∘++⁻ xs pxs)

  All-++⁻∘++⁺ : ∀ {m} {xs : Vec A m} {ys : Vec A n} →
                (p : All P xs × All P ys) →
                All-++⁻ xs (uncurry All-++⁺ p) ≡ p
  All-++⁻∘++⁺ ([]       , pys) = P.refl
  All-++⁻∘++⁺ (px ∷ pxs , pys) rewrite All-++⁻∘++⁺ (pxs , pys) = P.refl

  ++↔ : ∀ {m} {xs : Vec A m} {ys : Vec A n} →
        (All P xs × All P ys) ↔ All P (xs ++ ys)
  ++↔ {xs = xs} = record
    { to         = P.→-to-⟶ $ uncurry All-++⁺
    ; from       = P.→-to-⟶ $ All-++⁻ xs
    ; inverse-of = record
      { left-inverse-of  = All-++⁻∘++⁺
      ; right-inverse-of = All-++⁺∘++⁻ xs
      }
    }

------------------------------------------------------------------------
-- All and concat

module _ {a m p} {A : Set a} {P : A → Set p} where

  All-concat⁺ : ∀ {n} {xss : Vec (Vec A m) n} →
                  All (All P) xss → All P (concat xss)
  All-concat⁺ [] = []
  All-concat⁺ (pxs ∷ pxss) = All-++⁺ pxs (All-concat⁺ pxss)

  All-concat⁻ : ∀ {n} (xss : Vec (Vec A m) n) →
                  All P (concat xss) → All (All P) xss
  All-concat⁻ [] [] = []
  All-concat⁻ (xs ∷ xss) pxss = All-++ˡ⁻ xs pxss ∷ All-concat⁻ xss (All-++ʳ⁻ xs pxss)

------------------------------------------------------------------------
-- All₂ is DEPRECATED. Please use Data.Vec.Relation.InductivePointwise
-- directly.

open import Data.Vec.Relation.InductivePointwise using () renaming
  ( gmap   to All₂-map
  ; trans  to comp
  ; ++⁺    to All₂-++
  ; ++ˡ⁻    to All₂-++ˡ⁻
  ; ++ʳ⁻    to All₂-++ʳ⁺
  ; ++⁻     to All₂-++⁻
  ; concat⁺ to All₂-concat⁺
  ; concat⁻ to All₂-concat⁻
  ) public
