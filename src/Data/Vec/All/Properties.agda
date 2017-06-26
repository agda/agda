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
open import Relation.Unary using () renaming (_⊆_ to _⋐_)
open import Relation.Binary using (REL; Trans)
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

-- A variant of All-map for All₂.

All₂-map : ∀ {a b c d p} {A : Set a} {B : Set b} {C : Set c} {D : Set d}
           {P : C → D → Set p}
           {f₁ : A → C} {f₂ : B → D} {k} {xs : Vec A k} {ys : Vec B k} →
           All₂ (λ x y → P (f₁ x) (f₂ y)) xs ys →
           All₂ P (Vec.map f₁ xs) (Vec.map f₂ ys)
All₂-map []         = []
All₂-map (px ∷ pxs) = px ∷ All₂-map pxs

-- Abstract composition of binary relations lifted to All₂.

comp : ∀ {a b c p q r} {A : Set a} {B : Set b} {C : Set c}
       {P : A → B → Set p} {Q : B → C → Set q} {R : A → C → Set r} →
       Trans P Q R → ∀ {k} → Trans (All₂ P {k}) (All₂ Q) (All₂ R)
comp _⊙_ []           []           = []
comp _⊙_ (pxy ∷ pxys) (qzx ∷ qzxs) = pxy ⊙ qzx ∷ comp _⊙_ pxys qzxs

------------------------------------------------------------------------
-- Variants of gmap for All₂.
  
module _ {a b c p q} {A : Set a} {B : Set b} {C : Set c} where

  -- A variant of gmap₂ shifting two functions from the binary
  -- relation to the vector.
  
  gmap₂ : ∀ {d} {D : Set d} {P : A → B → Set p} {Q : C → D → Set q}
            {f₁ : A → C} {f₂ : B → D} →
          (∀ {x y} → P x y → Q (f₁ x) (f₂ y)) → ∀ {k xs ys} →
          All₂ P {k} xs ys → All₂ Q {k} (Vec.map f₁ xs) (Vec.map f₂ ys)
  gmap₂ g [] = []
  gmap₂ g (pxy ∷ pxys) = g pxy ∷ gmap₂ g pxys

  -- A variant of gmap₂ shifting only the first function from the binary
  -- relation to the vector.

  gmap₂₁ : ∀ {P : A → B → Set p} {Q : C → B → Set q} {f : A → C} →
           (∀ {x y} → P x y → Q (f x) y) → ∀ {k xs ys} →
           All₂ P {k} xs ys → All₂ Q {k} (Vec.map f xs) ys
  gmap₂₁ g [] = []
  gmap₂₁ g (pxy ∷ pxys) = g pxy ∷ gmap₂₁ g pxys

  -- A variant of gmap₂ shifting only the second function from the
  -- binary relation to the vector.
  
  gmap₂₂ : ∀ {P : A → B → Set p} {Q : A → C → Set q} {f : B → C} →
           (∀ {x y} → P x y → Q x (f y)) → ∀ {k xs ys} →
           All₂ P {k} xs ys → All₂ Q {k} xs (Vec.map f ys)
  gmap₂₂ g [] = []
  gmap₂₂ g (pxy ∷ pxys) = g pxy ∷ gmap₂₂ g pxys


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
-- All₂ and _++_

module _ {a b n p} {A : Set a} {B : Set b} {_~_ : REL A B p} where

  All₂-++⁺ : ∀ {m} {ws : Vec A m} {xs} {ys : Vec A n} {zs} →
           All₂ _~_ ws xs → All₂ _~_ ys zs →
           All₂ _~_ (ws ++ ys) (xs ++ zs)
  All₂-++⁺ []            ys~zs = ys~zs
  All₂-++⁺ (w~x ∷ ws~xs) ys~zs = w~x ∷ (All₂-++⁺ ws~xs ys~zs)

  All₂-++ˡ⁻ : ∀ {m} (ws : Vec A m) xs {ys : Vec A n} {zs} →
           All₂ _~_ (ws ++ ys) (xs ++ zs) → All₂ _~_ ws xs
  All₂-++ˡ⁻ []       []        _                    = []
  All₂-++ˡ⁻ (w ∷ ws) (x ∷ xs) (w~x ∷ ps) = w~x ∷ All₂-++ˡ⁻ ws xs ps

  All₂-++ʳ⁻ : ∀ {m} (ws : Vec A m) (xs : Vec B m) {ys : Vec A n} {zs} →
           All₂ _~_ (ws ++ ys) (xs ++ zs) → All₂ _~_ ys zs
  All₂-++ʳ⁻ [] [] ys~zs = ys~zs
  All₂-++ʳ⁻ (w ∷ ws) (x ∷ xs) (_ ∷ ps) = All₂-++ʳ⁻ ws xs ps

  All₂-++⁻ : ∀ {m} (ws : Vec A m) (xs : Vec B m) {ys : Vec A n} {zs} →
           All₂ _~_ (ws ++ ys) (xs ++ zs) →
           All₂ _~_ ws xs × All₂ _~_ ys zs
  All₂-++⁻ ws xs ps = All₂-++ˡ⁻ ws xs ps , All₂-++ʳ⁻ ws xs ps

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
-- All₂ and concat

module _ {a b m p} {A : Set a} {B : Set b} {_~_ : REL A B p} where

  All₂-concat⁺ : ∀ {n} {xss : Vec (Vec A m) n} {yss} →
                   All₂ (All₂ _~_) xss yss →
                   All₂ _~_ (concat xss) (concat yss)
  All₂-concat⁺ [] = []
  All₂-concat⁺ (xs~ys ∷ ps) = All₂-++⁺ xs~ys (All₂-concat⁺ ps)

  All₂-concat⁻ : ∀ {n} (xss : Vec (Vec A m) n) yss →
                   All₂ _~_ (concat xss) (concat yss) →
                   All₂ (All₂ _~_) xss yss
  All₂-concat⁻ []         []         [] = []
  All₂-concat⁻ (xs ∷ xss) (ys ∷ yss) ps =
    All₂-++ˡ⁻ xs ys ps ∷ All₂-concat⁻ xss yss (All₂-++ʳ⁻ xs ys ps)
  
