------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties related to Any
------------------------------------------------------------------------

-- The other modules under Data.List.Any also contain properties
-- related to Any.

module Data.List.Any.Properties where

open import Algebra
import Algebra.FunctionProperties as FP
open import Category.Monad
open import Data.Bool.Base using (Bool; false; true; T)
open import Data.Bool.Properties
open import Data.Empty
open import Data.List as List
open import Data.List.Any as Any using (Any; here; there)
open import Data.Product as Prod hiding (swap)
open import Data.Sum as Sum using (_⊎_; inj₁; inj₂; [_,_]′)
open import Function
open import Function.Equality using (_⟨$⟩_)
open import Function.Equivalence as Eq using (_⇔_; module Equivalence)
open import Function.Inverse as Inv using (_↔_; module Inverse)
open import Function.Related as Related using (Related)
open import Function.Related.TypeIsomorphisms
open import Level
open import Relation.Binary
import Relation.Binary.HeterogeneousEquality as H
open import Relation.Binary.Product.Pointwise
open import Relation.Binary.PropositionalEquality as P
  using (_≡_; refl; inspect) renaming ([_] to P[_])
open import Relation.Unary using (_⟨×⟩_; _⟨→⟩_) renaming (_⊆_ to _⋐_)
import Relation.Binary.Sigma.Pointwise as Σ
open import Relation.Binary.Sum

open Any.Membership-≡
open Related.EquationalReasoning
private
  module ×⊎ {k ℓ} = CommutativeSemiring (×⊎-CommutativeSemiring k ℓ)
  open module ListMonad {ℓ} = RawMonad (List.monad {ℓ = ℓ})

------------------------------------------------------------------------
-- Some lemmas related to map, find and lose
-- Any.map is functorial.

map-id : ∀ {a p} {A : Set a} {P : A → Set p} (f : P ⋐ P) {xs} →
         (∀ {x} (p : P x) → f p ≡ p) →
         (p : Any P xs) → Any.map f p ≡ p
map-id f hyp (here  p) = P.cong here (hyp p)
map-id f hyp (there p) = P.cong there $ map-id f hyp p

map-∘ : ∀ {a p q r}
          {A : Set a} {P : A → Set p} {Q : A → Set q} {R : A → Set r}
        (f : Q ⋐ R) (g : P ⋐ Q)
        {xs} (p : Any P xs) →
        Any.map (f ∘ g) p ≡ Any.map f (Any.map g p)
map-∘ f g (here  p) = refl
map-∘ f g (there p) = P.cong there $ map-∘ f g p

-- Lemmas relating map and find.

map∘find : ∀ {a p} {A : Set a} {P : A → Set p} {xs}
           (p : Any P xs) → let p′ = find p in
           {f : _≡_ (proj₁ p′) ⋐ P} →
           f refl ≡ proj₂ (proj₂ p′) →
           Any.map f (proj₁ (proj₂ p′)) ≡ p
map∘find (here  p) hyp = P.cong here  hyp
map∘find (there p) hyp = P.cong there (map∘find p hyp)

find∘map : ∀ {a p q} {A : Set a} {P : A → Set p} {Q : A → Set q}
           {xs : List A} (p : Any P xs) (f : P ⋐ Q) →
           find (Any.map f p) ≡ Prod.map id (Prod.map id f) (find p)
find∘map (here  p) f = refl
find∘map (there p) f rewrite find∘map p f = refl

-- find satisfies a simple equality when the predicate is a
-- propositional equality.

find-∈ : ∀ {a} {A : Set a} {x : A} {xs : List A} (x∈xs : x ∈ xs) →
         find x∈xs ≡ (x , x∈xs , refl)
find-∈ (here refl)  = refl
find-∈ (there x∈xs) rewrite find-∈ x∈xs = refl

-- find and lose are inverses (more or less).

lose∘find : ∀ {a p} {A : Set a} {P : A → Set p} {xs : List A}
            (p : Any P xs) →
            uncurry′ lose (proj₂ (find p)) ≡ p
lose∘find p = map∘find p P.refl

find∘lose : ∀ {a p} {A : Set a} (P : A → Set p) {x xs}
            (x∈xs : x ∈ xs) (pp : P x) →
            find {P = P} (lose x∈xs pp) ≡ (x , x∈xs , pp)
find∘lose P x∈xs p
  rewrite find∘map x∈xs (flip (P.subst P) p)
        | find-∈ x∈xs
        = refl

-- Any can be expressed using _∈_.

∃∈-Any : ∀ {a p} {A : Set a} {P : A → Set p} {xs} →
         (∃ λ x → x ∈ xs × P x) → Any P xs
∃∈-Any = uncurry′ lose ∘ proj₂

Any↔ : ∀ {a p} {A : Set a} {P : A → Set p} {xs} →
       (∃ λ x → x ∈ xs × P x) ↔ Any P xs
Any↔ {P = P} {xs} = record
  { to         = P.→-to-⟶ ∃∈-Any
  ; from       = P.→-to-⟶ (find {P = P})
  ; inverse-of = record
      { left-inverse-of  = λ p →
          find∘lose P (proj₁ (proj₂ p)) (proj₂ (proj₂ p))
      ; right-inverse-of = lose∘find
      }
  }

------------------------------------------------------------------------
-- Any is a congruence

Any-cong : ∀ {k ℓ} {A : Set ℓ} {P₁ P₂ : A → Set ℓ} {xs₁ xs₂ : List A} →
           (∀ x → Related k (P₁ x) (P₂ x)) → xs₁ ∼[ k ] xs₂ →
           Related k (Any P₁ xs₁) (Any P₂ xs₂)
Any-cong {P₁ = P₁} {P₂} {xs₁} {xs₂} P₁↔P₂ xs₁≈xs₂ =
  Any P₁ xs₁                ↔⟨ sym $ Any↔ {P = P₁} ⟩
  (∃ λ x → x ∈ xs₁ × P₁ x)  ∼⟨ Σ.cong Inv.id (xs₁≈xs₂ ×-cong P₁↔P₂ _) ⟩
  (∃ λ x → x ∈ xs₂ × P₂ x)  ↔⟨ Any↔ {P = P₂} ⟩
  Any P₂ xs₂                ∎

------------------------------------------------------------------------
-- Swapping

-- Nested occurrences of Any can sometimes be swapped. See also ×↔.

swap : ∀ {ℓ} {A B : Set ℓ} {P : A → B → Set ℓ} {xs ys} →
       Any (λ x → Any (P x) ys) xs ↔ Any (λ y → Any (flip P y) xs) ys
swap {ℓ} {P = P} {xs} {ys} =
  Any (λ x → Any (P x) ys) xs                ↔⟨ sym $ Any↔ {a = ℓ} {p = ℓ} ⟩
  (∃ λ x → x ∈ xs × Any (P x) ys)            ↔⟨ sym $ Σ.cong Inv.id (λ {x} → (x ∈ xs ∎) ⟨ ×⊎.*-cong {ℓ = ℓ} ⟩ Any↔ {a = ℓ} {p = ℓ}) ⟩
  (∃ λ x → x ∈ xs × ∃ λ y → y ∈ ys × P x y)  ↔⟨ Σ.cong {a₁ = ℓ} Inv.id (∃∃↔∃∃ {a = ℓ} {b = ℓ} {p = ℓ} _) ⟩
  (∃₂ λ x y → x ∈ xs × y ∈ ys × P x y)       ↔⟨ ∃∃↔∃∃ {a = ℓ} {b = ℓ} {p = ℓ} _ ⟩
  (∃₂ λ y x → x ∈ xs × y ∈ ys × P x y)       ↔⟨ Σ.cong Inv.id (λ {y} → Σ.cong Inv.id (λ {x} →
    (x ∈ xs × y ∈ ys × P x y)                     ↔⟨ sym $ ×⊎.*-assoc _ _ _ ⟩
    ((x ∈ xs × y ∈ ys) × P x y)                   ↔⟨ ×⊎.*-comm (x ∈ xs) (y ∈ ys) ⟨ ×⊎.*-cong ⟩ (P x y ∎) ⟩
    ((y ∈ ys × x ∈ xs) × P x y)                   ↔⟨ ×⊎.*-assoc _ _ _ ⟩
    (y ∈ ys × x ∈ xs × P x y)                     ∎)) ⟩
  (∃₂ λ y x → y ∈ ys × x ∈ xs × P x y)       ↔⟨ Σ.cong {a₁ = ℓ} Inv.id (∃∃↔∃∃ {a = ℓ} {b = ℓ} {p = ℓ} _) ⟩
  (∃ λ y → y ∈ ys × ∃ λ x → x ∈ xs × P x y)  ↔⟨ Σ.cong Inv.id (λ {y} → (y ∈ ys ∎) ⟨ ×⊎.*-cong {ℓ = ℓ} ⟩ Any↔ {a = ℓ} {p = ℓ}) ⟩
  (∃ λ y → y ∈ ys × Any (flip P y) xs)       ↔⟨ Any↔ {a = ℓ} {p = ℓ} ⟩
  Any (λ y → Any (flip P y) xs) ys           ∎

------------------------------------------------------------------------
-- Lemmas relating Any to ⊥

⊥↔Any⊥ : ∀ {a} {A : Set a} {xs : List A} → ⊥ ↔ Any (const ⊥) xs
⊥↔Any⊥ {A = A} = record
  { to         = P.→-to-⟶ (λ ())
  ; from       = P.→-to-⟶ (λ p → from p)
  ; inverse-of = record
    { left-inverse-of  = λ ()
    ; right-inverse-of = λ p → from p
    }
  }
  where
  from : {xs : List A} → Any (const ⊥) xs → ∀ {b} {B : Set b} → B
  from (here ())
  from (there p) = from p

⊥↔Any[] : ∀ {a} {A : Set a} {P : A → Set} → ⊥ ↔ Any P []
⊥↔Any[] = record
  { to         = P.→-to-⟶ (λ ())
  ; from       = P.→-to-⟶ (λ ())
  ; inverse-of = record
    { left-inverse-of  = λ ()
    ; right-inverse-of = λ ()
    }
  }

------------------------------------------------------------------------
-- Lemmas relating Any to sums and products

-- Sums commute with Any (for a fixed list).

⊎→ : ∀ {a p q} {A : Set a} {P : A → Set p} {Q : A → Set q} {xs}
     → Any P xs ⊎ Any Q xs → Any (λ x → P x ⊎ Q x) xs
⊎→ = [ Any.map inj₁ , Any.map inj₂ ]′

⊎← : ∀ {a p q} {A : Set a} {P : A → Set p} {Q : A → Set q} {xs}
     → Any (λ x → P x ⊎ Q x) xs → Any P xs ⊎ Any Q xs
⊎← (here (inj₁ p)) = inj₁ (here p)
⊎← (here (inj₂ q)) = inj₂ (here q)
⊎← (there p)       = Sum.map there there (⊎← p)

⊎↔ : ∀ {a p q} {A : Set a} {P : A → Set p} {Q : A → Set q} {xs} →
     (Any P xs ⊎ Any Q xs) ↔ Any (λ x → P x ⊎ Q x) xs
⊎↔ {P = P} {Q} = record
  { to         = P.→-to-⟶ ⊎→
  ; from       = P.→-to-⟶ ⊎←
  ; inverse-of = record
    { left-inverse-of  = from∘to
    ; right-inverse-of = to∘from
    }
  }
  where

  from∘to : ∀ {xs} (p : Any P xs ⊎ Any Q xs) → ⊎← (⊎→ p) ≡ p
  from∘to (inj₁ (here  p)) = P.refl
  from∘to (inj₁ (there p)) rewrite from∘to (inj₁ p) = P.refl
  from∘to (inj₂ (here  q)) = P.refl
  from∘to (inj₂ (there q)) rewrite from∘to (inj₂ q) = P.refl

  to∘from : ∀ {xs} (p : Any (λ x → P x ⊎ Q x) xs) →
            ⊎→ (⊎← p) ≡ p
  to∘from (here (inj₁ p)) = P.refl
  to∘from (here (inj₂ q)) = P.refl
  to∘from (there p) with ⊎← p | to∘from p
  to∘from (there .(Any.map inj₁ p)) | inj₁ p | P.refl = P.refl
  to∘from (there .(Any.map inj₂ q)) | inj₂ q | P.refl = P.refl


-- Products "commute" with Any.

×→ : ∀ {a b p q} {A : Set a} {B : Set b}
     {P : A → Set p} {Q : B → Set q} {xs : List A} {ys : List B}
     → Any P xs × Any Q ys → Any (λ x → Any (λ y → P x × Q y) ys) xs
×→ (p , q) = Any.map (λ p → Any.map (λ q → (p , q)) q) p

×← : ∀ {a b p q} {A : Set a} {B : Set b}
     {P : A → Set p} {Q : B → Set q} {xs : List A} {ys : List B}
     → Any (λ x → Any (λ y → P x × Q y) ys) xs → Any P xs × Any Q ys
×← pq with Prod.map id (Prod.map id find) (find pq)
... | (x , x∈xs , y , y∈ys , p , q) = (lose x∈xs p , lose y∈ys q)

×↔ : ∀ {a b p q} {A : Set a} {B : Set b}
     {P : A → Set p} {Q : B → Set q} {xs : List A} {ys : List B} →
     (Any P xs × Any Q ys) ↔ Any (λ x → Any (λ y → P x × Q y) ys) xs
×↔ {P = P} {Q} {xs} {ys} = record
  { to         = P.→-to-⟶ ×→
  ; from       = P.→-to-⟶ ×←
  ; inverse-of = record
    { left-inverse-of  = from∘to
    ; right-inverse-of = to∘from
    }
  }
  where
  from∘to : ∀ pq → ×← (×→ pq) ≡ pq
  from∘to (p , q)
    rewrite find∘map {Q = λ x → Any (λ y → P x × Q y) ys}
                     p (λ p → Any.map (λ q → (p , q)) q)
          | find∘map {Q = λ y → P (proj₁ (find p)) × Q y}
                     q (λ q → proj₂ (proj₂ (find p)) , q)
          | lose∘find p
          | lose∘find q
      = refl

  to∘from : ∀ pq → ×→ (×← pq) ≡ pq
  to∘from pq
    with find pq
       | (λ (f : _≡_ (proj₁ (find pq)) ⋐ _) → map∘find pq {f})
  ... | (x , x∈xs , pq′) | lem₁
    with find pq′
       | (λ (f : _≡_ (proj₁ (find pq′)) ⋐ _) → map∘find pq′ {f})
  ... | (y , y∈ys , p , q) | lem₂
    rewrite P.sym $ map-∘ {R = λ x → Any (λ y → P x × Q y) ys}
                          (λ p → Any.map (λ q → p , q) (lose y∈ys q))
                          (λ y → P.subst P y p)
                          x∈xs
      = lem₁ _ helper
    where
    helper : Any.map (λ q → p , q) (lose y∈ys q) ≡ pq′
    helper rewrite P.sym $ map-∘ {R = λ y → P x × Q y}
                                 (λ q → p , q)
                                 (λ y → P.subst Q y q)
                                 y∈ys
      = lem₂ _ refl

------------------------------------------------------------------------
-- Invertible introduction (⁺) and elimination (⁻) rules for various
-- list functions

-- map.

map⁺ : ∀ {a b p} {A : Set a} {B : Set b} {P : B → Set p}
       {f : A → B} {xs} → Any (P ∘ f) xs → Any P (List.map f xs)
map⁺ (here p)  = here p
map⁺ (there p) = there $ map⁺ p

map⁻ : ∀ {a b p} {A : Set a} {B : Set b} {P : B → Set p}
       {f : A → B} {xs} →
       Any P (List.map f xs) → Any (P ∘ f) xs
map⁻ {xs = []}     ()
map⁻ {xs = x ∷ xs} (here p)  = here p
map⁻ {xs = x ∷ xs} (there p) = there $ map⁻ p

map⁺∘map⁻ : ∀ {a b p} {A : Set a} {B : Set b} {P : B → Set p}
            {f : A → B} {xs} →
            (p : Any P (List.map f xs)) →
            map⁺ (map⁻ p) ≡ p
map⁺∘map⁻ {xs = []}     ()
map⁺∘map⁻ {xs = x ∷ xs} (here  p) = refl
map⁺∘map⁻ {xs = x ∷ xs} (there p) = P.cong there (map⁺∘map⁻ p)

map⁻∘map⁺ : ∀ {a b p} {A : Set a} {B : Set b} (P : B → Set p)
            {f : A → B} {xs} →
            (p : Any (P ∘ f) xs) →
            map⁻ {P = P} (map⁺ p) ≡ p
map⁻∘map⁺ P (here  p) = refl
map⁻∘map⁺ P (there p) = P.cong there (map⁻∘map⁺ P p)

map↔ : ∀ {a b p} {A : Set a} {B : Set b} {P : B → Set p}
         {f : A → B} {xs} →
       Any (P ∘ f) xs ↔ Any P (List.map f xs)
map↔ {P = P} {f = f} = record
  { to         = P.→-to-⟶ $ map⁺ {P = P} {f = f}
  ; from       = P.→-to-⟶ $ map⁻ {P = P} {f = f}
  ; inverse-of = record
    { left-inverse-of  = map⁻∘map⁺ P
    ; right-inverse-of = map⁺∘map⁻
    }
  }

-- _++_.

++⁺ˡ : ∀ {a p} {A : Set a} {P : A → Set p} {xs ys} →
      Any P xs → Any P (xs ++ ys)
++⁺ˡ (here p)  = here p
++⁺ˡ (there p) = there (++⁺ˡ p)

++⁺ʳ : ∀ {a p} {A : Set a} {P : A → Set p} xs {ys} →
       Any P ys → Any P (xs ++ ys)
++⁺ʳ []       p = p
++⁺ʳ (x ∷ xs) p = there (++⁺ʳ xs p)

++⁻ : ∀ {a p} {A : Set a} {P : A → Set p} xs {ys} →
      Any P (xs ++ ys) → Any P xs ⊎ Any P ys
++⁻ []       p         = inj₂ p
++⁻ (x ∷ xs) (here p)  = inj₁ (here p)
++⁻ (x ∷ xs) (there p) = Sum.map there id (++⁻ xs p)

++⁺∘++⁻ : ∀ {a p} {A : Set a} {P : A → Set p} xs {ys}
          (p : Any P (xs ++ ys)) →
          [ ++⁺ˡ , ++⁺ʳ xs ]′ (++⁻ xs p) ≡ p
++⁺∘++⁻ []       p         = refl
++⁺∘++⁻ (x ∷ xs) (here  p) = refl
++⁺∘++⁻ (x ∷ xs) (there p) with ++⁻ xs p | ++⁺∘++⁻ xs p
++⁺∘++⁻ (x ∷ xs) (there p) | inj₁ p′ | ih = P.cong there ih
++⁺∘++⁻ (x ∷ xs) (there p) | inj₂ p′ | ih = P.cong there ih

++⁻∘++⁺ : ∀ {a p} {A : Set a} {P : A → Set p} xs {ys}
          (p : Any P xs ⊎ Any P ys) →
          ++⁻ xs ([ ++⁺ˡ , ++⁺ʳ xs ]′ p) ≡ p
++⁻∘++⁺ []            (inj₁ ())
++⁻∘++⁺ []            (inj₂ p)         = refl
++⁻∘++⁺ (x ∷ xs)      (inj₁ (here  p)) = refl
++⁻∘++⁺ (x ∷ xs) {ys} (inj₁ (there p)) rewrite ++⁻∘++⁺ xs {ys} (inj₁ p) = refl
++⁻∘++⁺ (x ∷ xs)      (inj₂ p)         rewrite ++⁻∘++⁺ xs      (inj₂ p) = refl

++ˡ = ++⁺ˡ
++ʳ = ++⁺ʳ

++↔ : ∀ {a p} {A : Set a} {P : A → Set p} {xs ys} →
      (Any P xs ⊎ Any P ys) ↔ Any P (xs ++ ys)
++↔ {P = P} {xs = xs} = record
  { to         = P.→-to-⟶ [ ++⁺ˡ {P = P}, ++⁺ʳ {P = P} xs ]′
  ; from       = P.→-to-⟶ $ ++⁻ {P = P} xs
  ; inverse-of = record
    { left-inverse-of  = ++⁻∘++⁺ xs
    ; right-inverse-of = ++⁺∘++⁻ xs
    }
  }

-- return.

return⁺ : ∀ {a p} {A : Set a} {P : A → Set p} {x} →
          P x → Any P (return x)
return⁺ = here

return⁻ : ∀ {a p} {A : Set a} {P : A → Set p} {x} →
          Any P (return x) → P x
return⁻ (here p)   = p
return⁻ (there ())

return⁺∘return⁻ : ∀ {a p} {A : Set a} {P : A → Set p} {x}
                  (p : Any P (return x)) →
                  return⁺ (return⁻ p) ≡ p
return⁺∘return⁻ (here p)   = refl
return⁺∘return⁻ (there ())

return⁻∘return⁺ : ∀ {a p} {A : Set a} (P : A → Set p) {x} (p : P x) →
                  return⁻ {P = P} (return⁺ p) ≡ p
return⁻∘return⁺ P p = refl

return↔ : ∀ {a p} {A : Set a} {P : A → Set p} {x} →
          P x ↔ Any P (return x)
return↔ {P = P} = record
  { to         = P.→-to-⟶ $ return⁺ {P = P}
  ; from       = P.→-to-⟶ $ return⁻ {P = P}
  ; inverse-of = record
    { left-inverse-of  = return⁻∘return⁺ P
    ; right-inverse-of = return⁺∘return⁻
    }
  }

-- _∷_.

∷↔ : ∀ {a p} {A : Set a} (P : A → Set p) {x xs} →
     (P x ⊎ Any P xs) ↔ Any P (x ∷ xs)
∷↔ P {x} {xs} =
  (P x         ⊎ Any P xs)  ↔⟨ return↔ {P = P} ⊎-cong (Any P xs ∎) ⟩
  (Any P [ x ] ⊎ Any P xs)  ↔⟨ ++↔ {P = P} {xs = [ x ]} ⟩
  Any P (x ∷ xs)            ∎

-- concat.

concat⁺ : ∀ {a p} {A : Set a} {P : A → Set p} {xss} →
          Any (Any P) xss → Any P (concat xss)
concat⁺ (here p)           = ++⁺ˡ p
concat⁺ (there {x = xs} p) = ++⁺ʳ xs (concat⁺ p)

concat⁻ : ∀ {a p} {A : Set a} {P : A → Set p} xss →
          Any P (concat xss) → Any (Any P) xss
concat⁻ []               ()
concat⁻ ([]       ∷ xss) p         = there $ concat⁻ xss p
concat⁻ ((x ∷ xs) ∷ xss) (here  p) = here (here p)
concat⁻ ((x ∷ xs) ∷ xss) (there p) with concat⁻ (xs ∷ xss) p
... | here  p′ = here (there p′)
... | there p′ = there p′

concat⁻∘++⁺ˡ : ∀ {a p} {A : Set a} {P : A → Set p} {xs} xss (p : Any P xs) →
               concat⁻ (xs ∷ xss) (++⁺ˡ p) ≡ here p
concat⁻∘++⁺ˡ xss (here  p) = refl
concat⁻∘++⁺ˡ xss (there p) rewrite concat⁻∘++⁺ˡ xss p = refl

concat⁻∘++⁺ʳ : ∀ {a p} {A : Set a} {P : A → Set p} xs xss (p : Any P (concat xss)) →
                 concat⁻ (xs ∷ xss) (++⁺ʳ xs p) ≡ there (concat⁻ xss p)
concat⁻∘++⁺ʳ []       xss p = refl
concat⁻∘++⁺ʳ (x ∷ xs) xss p rewrite concat⁻∘++⁺ʳ xs xss p = refl

concat⁺∘concat⁻ : ∀ {a p} {A : Set a} {P : A → Set p} xss (p : Any P (concat xss)) →
                    concat⁺ (concat⁻ xss p) ≡ p
concat⁺∘concat⁻ []               ()
concat⁺∘concat⁻ ([]       ∷ xss) p         = concat⁺∘concat⁻ xss p
concat⁺∘concat⁻ ((x ∷ xs) ∷ xss) (here p)  = refl
concat⁺∘concat⁻ ((x ∷ xs) ∷ xss) (there p)
  with concat⁻ (xs ∷ xss) p | concat⁺∘concat⁻ (xs ∷ xss) p
concat⁺∘concat⁻ ((x ∷ xs) ∷ xss) (there .(++⁺ˡ p′))              | here  p′ | refl = refl
concat⁺∘concat⁻ ((x ∷ xs) ∷ xss) (there .(++⁺ʳ xs (concat⁺ p′))) | there p′ | refl = refl

concat⁻∘concat⁺ : ∀ {a p} {A : Set a} {P : A → Set p} {xss} (p : Any (Any P) xss) →
                    concat⁻ xss (concat⁺ p) ≡ p
concat⁻∘concat⁺ (here                      p) = concat⁻∘++⁺ˡ _ p
concat⁻∘concat⁺ (there {x = xs} {xs = xss} p)
  rewrite concat⁻∘++⁺ʳ xs xss (concat⁺ p) =
    P.cong there $ concat⁻∘concat⁺ p

concat↔ : ∀ {a p} {A : Set a} {P : A → Set p} {xss} →
          Any (Any P) xss ↔ Any P (concat xss)
concat↔ {P = P} {xss = xss} = record
  { to         = P.→-to-⟶ $ concat⁺ {P = P}
  ; from       = P.→-to-⟶ $ concat⁻ {P = P} xss
  ; inverse-of = record
    { left-inverse-of  = concat⁻∘concat⁺
    ; right-inverse-of = concat⁺∘concat⁻ xss
    }
  }

-- _>>=_.

>>=↔ : ∀ {ℓ p} {A B : Set ℓ} {P : B → Set p} {xs} {f : A → List B} →
       Any (Any P ∘ f) xs ↔ Any P (xs >>= f)
>>=↔ {P = P} {xs} {f} =
  Any (Any P ∘ f) xs           ↔⟨ map↔ {P = Any P} {f = f} ⟩
  Any (Any P) (List.map f xs)  ↔⟨ concat↔ {P = P} ⟩
  Any P (xs >>= f)             ∎

-- _⊛_.

⊛↔ : ∀ {ℓ} {A B : Set ℓ} {P : B → Set ℓ}
       {fs : List (A → B)} {xs : List A} →
     Any (λ f → Any (P ∘ f) xs) fs ↔ Any P (fs ⊛ xs)
⊛↔ {ℓ} {P = P} {fs} {xs} =
  Any (λ f → Any (P ∘ f) xs) fs               ↔⟨ Any-cong (λ _ → Any-cong (λ _ → return↔ {a = ℓ} {p = ℓ}) (_ ∎)) (_ ∎) ⟩
  Any (λ f → Any (Any P ∘ return ∘ f) xs) fs  ↔⟨ Any-cong (λ _ → >>=↔ {ℓ = ℓ} {p = ℓ}) (_ ∎) ⟩
  Any (λ f → Any P (xs >>= return ∘ f)) fs    ↔⟨ >>=↔ {ℓ = ℓ} {p = ℓ} ⟩
  Any P (fs ⊛ xs)                             ∎

-- An alternative introduction rule for _⊛_.

⊛⁺′ : ∀ {ℓ} {A B : Set ℓ} {P : A → Set ℓ} {Q : B → Set ℓ}
      {fs : List (A → B)} {xs} →
      Any (P ⟨→⟩ Q) fs → Any P xs → Any Q (fs ⊛ xs)
⊛⁺′ {ℓ} pq p =
  Inverse.to (⊛↔ {ℓ = ℓ}) ⟨$⟩
    Any.map (λ pq → Any.map (λ {x} → pq {x}) p) pq

-- _⊗_.

⊗↔ : ∀ {ℓ} {A B : Set ℓ} {P : A × B → Set ℓ}
       {xs : List A} {ys : List B} →
     Any (λ x → Any (λ y → P (x , y)) ys) xs ↔ Any P (xs ⊗ ys)
⊗↔ {ℓ} {P = P} {xs} {ys} =
  Any (λ x → Any (λ y → P (x , y)) ys) xs                             ↔⟨ return↔ {a = ℓ} {p = ℓ} ⟩
  Any (λ _,_ → Any (λ x → Any (λ y → P (x , y)) ys) xs) (return _,_)  ↔⟨ ⊛↔ ⟩
  Any (λ x, → Any (P ∘ x,) ys) (_,_ <$> xs)                           ↔⟨ ⊛↔ ⟩
  Any P (xs ⊗ ys)                                                     ∎

⊗↔′ : {A B : Set} {P : A → Set} {Q : B → Set}
      {xs : List A} {ys : List B} →
      (Any P xs × Any Q ys) ↔ Any (P ⟨×⟩ Q) (xs ⊗ ys)
⊗↔′ {P = P} {Q} {xs} {ys} =
  (Any P xs × Any Q ys)                    ↔⟨ ×↔ ⟩
  Any (λ x → Any (λ y → P x × Q y) ys) xs  ↔⟨ ⊗↔ ⟩
  Any (P ⟨×⟩ Q) (xs ⊗ ys)                  ∎

-- map-with-∈.

map-with-∈↔ :
  ∀ {a b p} {A : Set a} {B : Set b} {P : B → Set p} {xs : List A}
    {f : ∀ {x} → x ∈ xs → B} →
  (∃₂ λ x (x∈xs : x ∈ xs) → P (f x∈xs)) ↔ Any P (map-with-∈ xs f)
map-with-∈↔ {A = A} {B} {P} = record
  { to         = P.→-to-⟶ (map-with-∈⁺ _)
  ; from       = P.→-to-⟶ (map-with-∈⁻ _ _)
  ; inverse-of = record
    { left-inverse-of  = from∘to _
    ; right-inverse-of = to∘from _ _
    }
  }
  where
  map-with-∈⁺ : ∀ {xs : List A}
                (f : ∀ {x} → x ∈ xs → B) →
                (∃₂ λ x (x∈xs : x ∈ xs) → P (f x∈xs)) →
                Any P (map-with-∈ xs f)
  map-with-∈⁺ f (_ , here refl  , p) = here p
  map-with-∈⁺ f (_ , there x∈xs , p) =
    there $ map-with-∈⁺ (f ∘ there) (_ , x∈xs , p)

  map-with-∈⁻ : ∀ (xs : List A)
                (f : ∀ {x} → x ∈ xs → B) →
                Any P (map-with-∈ xs f) →
                ∃₂ λ x (x∈xs : x ∈ xs) → P (f x∈xs)
  map-with-∈⁻ []       f ()
  map-with-∈⁻ (y ∷ xs) f (here  p) = (y , here refl , p)
  map-with-∈⁻ (y ∷ xs) f (there p) =
    Prod.map id (Prod.map there id) $ map-with-∈⁻ xs (f ∘ there) p

  from∘to : ∀ {xs : List A} (f : ∀ {x} → x ∈ xs → B)
            (p : ∃₂ λ x (x∈xs : x ∈ xs) → P (f x∈xs)) →
            map-with-∈⁻ xs f (map-with-∈⁺ f p) ≡ p
  from∘to f (_ , here refl  , p) = refl
  from∘to f (_ , there x∈xs , p)
    rewrite from∘to (f ∘ there) (_ , x∈xs , p) = refl

  to∘from : ∀ (xs : List A) (f : ∀ {x} → x ∈ xs → B)
            (p : Any P (map-with-∈ xs f)) →
            map-with-∈⁺ f (map-with-∈⁻ xs f p) ≡ p
  to∘from []       f ()
  to∘from (y ∷ xs) f (here  p) = refl
  to∘from (y ∷ xs) f (there p) =
    P.cong there $ to∘from xs (f ∘ there) p

------------------------------------------------------------------------
-- Any and any are related via T

-- These introduction and elimination rules are not inverses, though.

any⁺ : ∀ {a} {A : Set a} (p : A → Bool) {xs} →
       Any (T ∘ p) xs → T (any p xs)
any⁺ p (here  px)          = Equivalence.from T-∨ ⟨$⟩ inj₁ px
any⁺ p (there {x = x} pxs) with p x
... | true  = _
... | false = any⁺ p pxs

any⁻ : ∀ {a} {A : Set a} (p : A → Bool) xs →
       T (any p xs) → Any (T ∘ p) xs
any⁻ p []       ()
any⁻ p (x ∷ xs) px∷xs with p x | inspect p x
any⁻ p (x ∷ xs) px∷xs | true  | P[ eq ] = here (Equivalence.from T-≡ ⟨$⟩ eq)
any⁻ p (x ∷ xs) px∷xs | false | _       = there (any⁻ p xs px∷xs)

any⇔ : ∀ {a} {A : Set a} {p : A → Bool} {xs} →
       Any (T ∘ p) xs ⇔ T (any p xs)
any⇔ = Eq.equivalence (any⁺ _) (any⁻ _ _)

------------------------------------------------------------------------
-- _++_ is commutative

++-comm : ∀ {a p} {A : Set a} {P : A → Set p} xs ys →
            Any P (xs ++ ys) → Any P (ys ++ xs)
++-comm xs ys = [ ++⁺ʳ ys , ++⁺ˡ ]′ ∘ ++⁻ xs

++-comm∘++-comm : ∀ {a p} {A : Set a} {P : A → Set p}
                  xs {ys} (p : Any P (xs ++ ys)) →
                  ++-comm ys xs (++-comm xs ys p) ≡ p
++-comm∘++-comm [] {ys} p
  rewrite ++⁻∘++⁺ ys {ys = []} (inj₁ p) = P.refl
++-comm∘++-comm {P = P} (x ∷ xs) {ys} (here p)
  rewrite ++⁻∘++⁺ {P = P} ys {ys = x ∷ xs} (inj₂ (here p)) = P.refl
++-comm∘++-comm (x ∷ xs)      (there p) with ++⁻ xs p | ++-comm∘++-comm xs p
++-comm∘++-comm (x ∷ xs) {ys} (there .([ ++⁺ʳ xs , ++⁺ˡ ]′ (++⁻ ys (++⁺ʳ ys p))))
  | inj₁ p | P.refl
  rewrite ++⁻∘++⁺ ys (inj₂                 p)
        | ++⁻∘++⁺ ys (inj₂ $ there {x = x} p) = P.refl
++-comm∘++-comm (x ∷ xs) {ys} (there .([ ++⁺ʳ xs , ++⁺ˡ ]′ (++⁻ ys (++⁺ˡ p))))
  | inj₂ p | P.refl
  rewrite ++⁻∘++⁺ ys {ys =     xs} (inj₁ p)
        | ++⁻∘++⁺ ys {ys = x ∷ xs} (inj₁ p) = P.refl

++↔++ : ∀ {a p} {A : Set a} {P : A → Set p} xs ys →
        Any P (xs ++ ys) ↔ Any P (ys ++ xs)
++↔++ {P = P} xs ys = record
  { to         = P.→-to-⟶ $ ++-comm {P = P} xs ys
  ; from       = P.→-to-⟶ $ ++-comm {P = P} ys xs
  ; inverse-of = record
    { left-inverse-of  = ++-comm∘++-comm xs
    ; right-inverse-of = ++-comm∘++-comm ys
    }
  }
