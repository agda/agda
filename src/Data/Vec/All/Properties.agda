------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties related to All
------------------------------------------------------------------------

module Data.Vec.All.Properties where

open import Data.Vec as Vec using (Vec; []; _∷_; zip)
open import Data.Vec.Properties using (map-id; lookup-zip)
open import Data.Product as Prod using (_×_; _,_; uncurry; uncurry′)
open import Data.Vec using (Vec; _++_)
open import Data.Vec.All as All using (All; All₂; []; _∷_)
open import Function
open import Function.Inverse using (_↔_)
open import Relation.Unary using () renaming (_⊆_ to _⋐_)
open import Relation.Binary.PropositionalEquality as P using (_≡_)

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

-- A variant of All-map tailored to All₂.

All₂-map : ∀ {a b p} {A₁ A₂ : Set a} {B₁ B₂ : Set b} {P : B₁ → B₂ → Set p}
           {f₁ : A₁ → B₁} {f₂ : A₂ → B₂} {k} {xs : Vec A₁ k} {ys : Vec A₂ k} →
           All₂ (λ x y → P (f₁ x) (f₂ y)) xs ys →
           All₂ P (Vec.map f₁ xs) (Vec.map f₂ ys)
All₂-map {xs = []}    {ys = []}    []         = []
All₂-map {xs = _ ∷ _} {ys = _ ∷ _} (px ∷ pxs) = px ∷ All₂-map pxs

-- A variant of gmap tailored to All₂.

gmap₂ : ∀ {a b p q} {A₁ A₂ : Set a} {B₁ B₂ : Set b}
          {P : A₁ → A₂ → Set p} {Q : B₁ → B₂ → Set q}
          {f₁ : A₁ → B₁} {f₂ : A₂ → B₂} →
        (∀ {x y} → P x y → Q (f₁ x) (f₂ y)) → ∀ {k xs ys} →
        All₂ P {k} xs ys → All₂ Q {k} (Vec.map f₁ xs) (Vec.map f₂ ys)
gmap₂ g = All₂-map ∘ All.map g

-- A variant of gmap₂ shifting only the first function from the binary
-- relation to the vector.

gmap₂₁ : ∀ {a p q} {A₁ A₂ : Set a} {B : Set a}
           {P : A₁ → A₂ → Set p} {Q : B → A₂ → Set q} {f : A₁ → B} →
         (∀ {x y} → P x y → Q (f x) y) → ∀ {k xs ys} →
         All₂ P {k} xs ys → All₂ Q {k} (Vec.map f xs) ys
gmap₂₁ g = P.subst (All₂ _ _) (map-id _) ∘ All₂-map {f₂ = id} ∘ All.map g

-- A variant of gmap₂ shifting only the second function from the
-- binary relation to the vector.

gmap₂₂ : ∀ {a p q} {A₁ A₂ : Set a} {B : Set a}
           {P : A₁ → A₂ → Set p} {Q : A₁ → B → Set q} {f : A₂ → B} →
         (∀ {x y} → P x y → Q x (f y)) → ∀ {k xs ys} →
         All₂ P {k} xs ys → All₂ Q {k} xs (Vec.map f ys)
gmap₂₂ g =
  P.subst (flip (All₂ _) _) (map-id _) ∘ All₂-map {f₁ = id} ∘ All.map g

-- Abstract composition of binary relations lifted to All₂.

comp : ∀ {a p} {A : Set a} {B : Set a} {C : Set a}
       {P : A → B → Set p} {Q : B → C → Set p} {R : A → C → Set p} →
       (∀ {x y z} → P x y → Q y z → R x z) →
       ∀ {k xs ys zs} → All₂ P {k} xs ys → All₂ Q {k} ys zs → All₂ R {k} xs zs
comp _⊙_ {xs = []}     {[]}     {[]}     []           []           = []
comp _⊙_ {xs = x ∷ xs} {y ∷ ys} {z ∷ zs} (pxy ∷ pxys) (qzx ∷ qzxs) =
  pxy ⊙ qzx ∷ comp _⊙_ pxys qzxs

-- All P (xs ++ ys) is isomorphic to All P xs and All P ys.

private

  ++⁺ : ∀ {a p} {A : Set a} {P : A → Set p} {k i}
        {xs : Vec A k} {ys : Vec A i} →
        All P xs → All P ys → All P (xs ++ ys)
  ++⁺ []         pys = pys
  ++⁺ (px ∷ pxs) pys = px ∷ ++⁺ pxs pys

  ++⁻ : ∀ {a p} {A : Set a} {P : A → Set p} {k i}
        (xs : Vec A k) {ys : Vec A i} →
        All P (xs ++ ys) → All P xs × All P ys
  ++⁻ []       p          = [] , p
  ++⁻ (x ∷ xs) (px ∷ pxs) = Prod.map (_∷_ px) id $ ++⁻ _ pxs

  ++⁺∘++⁻ : ∀ {a p} {A : Set a} {P : A → Set p} {k i}
            (xs : Vec A k) {ys : Vec A i} (p : All P (xs ++ ys)) →
            uncurry′ ++⁺ (++⁻ xs p) ≡ p
  ++⁺∘++⁻ []       p          = P.refl
  ++⁺∘++⁻ (x ∷ xs) (px ∷ pxs) = P.cong (_∷_ px) $ ++⁺∘++⁻ xs pxs

  ++⁻∘++⁺ : ∀ {a p} {A : Set a} {P : A → Set p} {k i}
            {xs : Vec A k} {ys : Vec A i} (p : All P xs × All P ys) →
            ++⁻ xs (uncurry ++⁺ p) ≡ p
  ++⁻∘++⁺ ([]       , pys) = P.refl
  ++⁻∘++⁺ (px ∷ pxs , pys) rewrite ++⁻∘++⁺ (pxs , pys) = P.refl

++↔ : ∀ {a p} {A : Set a} {P : A → Set p} {k i} {xs : Vec A k} {ys : Vec A i} →
      (All P xs × All P ys) ↔ All P (xs ++ ys)
++↔ {P = P} {xs = xs} = record
  { to         = P.→-to-⟶ $ uncurry ++⁺
  ; from       = P.→-to-⟶ $ ++⁻ xs
  ; inverse-of = record
    { left-inverse-of  = ++⁻∘++⁺
    ; right-inverse-of = ++⁺∘++⁻ xs
    }
  }
