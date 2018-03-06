------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties related to Any
------------------------------------------------------------------------

-- The other modules under Data.List.Any also contain properties
-- related to Any.

module Data.List.Any.Properties where

open import Algebra
open import Category.Monad
open import Data.Bool.Base using (Bool; false; true; T)
open import Data.Bool.Properties
open import Data.Empty using (⊥)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.List as List
open import Data.List.Categorical using (monad)
open import Data.List.Any as Any using (Any; here; there)
open import Data.List.Any.Membership.Propositional
open import Data.List.Relation.Pointwise
  using (Pointwise; []; _∷_)
open import Data.Nat using (zero; suc; _<_; z≤n; s≤s)
open import Data.Maybe as Maybe using (Maybe; just; nothing)
open import Data.Product as Prod
  using (_×_; _,_; ∃; ∃₂; proj₁; proj₂; uncurry′)
open import Data.Product.Relation.Pointwise.NonDependent
  using (_×-cong_)
import Data.Product.Relation.Pointwise.Dependent as Σ
open import Data.Sum as Sum using (_⊎_; inj₁; inj₂; [_,_]′)
open import Data.Sum.Relation.General
open import Function
open import Function.Equality using (_⟨$⟩_)
open import Function.Equivalence as Eq using (_⇔_; module Equivalence)
open import Function.Inverse as Inv using (_↔_; module Inverse)
open import Function.Related as Related using (Related)
open import Relation.Binary
open import Relation.Binary.PropositionalEquality as P
  using (_≡_; refl; inspect)
open import Relation.Unary
  using (Pred; _⟨×⟩_; _⟨→⟩_) renaming (_⊆_ to _⋐_)

open Related.EquationalReasoning
private
  open module ListMonad {ℓ} = RawMonad (monad {ℓ = ℓ})

------------------------------------------------------------------------
-- If a predicate P respects the underlying equality then Any P
-- respects the list equality.

lift-resp : ∀ {a p ℓ} {A : Set a} {P : A → Set p} {_≈_ : Rel A ℓ} →
            P Respects _≈_ → (Any P) Respects (Pointwise _≈_)
lift-resp resp []            ()
lift-resp resp (x≈y ∷ xs≈ys) (here px)   = here (resp x≈y px)
lift-resp resp (x≈y ∷ xs≈ys) (there pxs) =
  there (lift-resp resp xs≈ys pxs)

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

swap : ∀ {a b ℓ} {A : Set a} {B : Set b} {P : A → B → Set ℓ} {xs ys} →
        Any (λ x → Any (P x) ys) xs → Any (λ y → Any (flip P y) xs) ys
swap (here  pys)  = Any.map here pys
swap (there pxys) = Any.map there (swap pxys)

swap-there : ∀ {a b ℓ} {A : Set a} {B : Set b} {P : A → B → Set ℓ}
             {x xs ys} → (any : Any (λ x → Any (P x) ys) xs) →
             swap (Any.map (there {x = x}) any) ≡ there (swap any)
swap-there (here  pys)  = refl
swap-there (there pxys) = P.cong (Any.map there) (swap-there pxys)

swap-invol : ∀ {a b ℓ} {A : Set a} {B : Set b} {P : A → B → Set ℓ}
             {xs ys} → (any : Any (λ x → Any (P x) ys) xs) →
             swap (swap any) ≡ any
swap-invol (here (here px))   = refl
swap-invol (here (there pys)) =
  P.cong (Any.map there) (swap-invol (here pys))
swap-invol (there pxys)       =
  P.trans (swap-there (swap pxys)) (P.cong there (swap-invol pxys))

swap↔ : ∀ {ℓ} {A B : Set ℓ} {P : A → B → Set ℓ} {xs ys} →
       Any (λ x → Any (P x) ys) xs ↔ Any (λ y → Any (flip P y) xs) ys
swap↔ {P = P} = record
  { to         = P.→-to-⟶ swap
  ; from       = P.→-to-⟶ swap
  ; inverse-of = record
    { left-inverse-of  = swap-invol
    ; right-inverse-of = swap-invol
    }
  }

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
-- Lemmas relating Any to ⊤

-- These introduction and elimination rules are not inverses, though.

module _ {a} {A : Set a} where

  any⁺ : ∀ (p : A → Bool) {xs} → Any (T ∘ p) xs → T (any p xs)
  any⁺ p (here  px)          = Equivalence.from T-∨ ⟨$⟩ inj₁ px
  any⁺ p (there {x = x} pxs) with p x
  ... | true  = _
  ... | false = any⁺ p pxs

  any⁻ : ∀ (p : A → Bool) xs → T (any p xs) → Any (T ∘ p) xs
  any⁻ p []       ()
  any⁻ p (x ∷ xs) px∷xs with p x | inspect p x
  any⁻ p (x ∷ xs) px∷xs | true  | P.[ eq ] = here (Equivalence.from T-≡ ⟨$⟩ eq)
  any⁻ p (x ∷ xs) px∷xs | false | _       = there (any⁻ p xs px∷xs)

  any⇔ : ∀ {p : A → Bool} {xs} → Any (T ∘ p) xs ⇔ T (any p xs)
  any⇔ = Eq.equivalence (any⁺ _) (any⁻ _ _)

------------------------------------------------------------------------
-- Sums commute with Any

module _ {a p q} {A : Set a} {P : A → Set p} {Q : A → Set q} where

  Any-⊎⁺ : ∀ {xs} → Any P xs ⊎ Any Q xs → Any (λ x → P x ⊎ Q x) xs
  Any-⊎⁺ = [ Any.map inj₁ , Any.map inj₂ ]′

  Any-⊎⁻ : ∀ {xs} → Any (λ x → P x ⊎ Q x) xs → Any P xs ⊎ Any Q xs
  Any-⊎⁻ (here (inj₁ p)) = inj₁ (here p)
  Any-⊎⁻ (here (inj₂ q)) = inj₂ (here q)
  Any-⊎⁻ (there p)       = Sum.map there there (Any-⊎⁻ p)

  ⊎↔ : ∀ {xs} → (Any P xs ⊎ Any Q xs) ↔ Any (λ x → P x ⊎ Q x) xs
  ⊎↔ = record
    { to         = P.→-to-⟶ Any-⊎⁺
    ; from       = P.→-to-⟶ Any-⊎⁻
    ; inverse-of = record
      { left-inverse-of  = from∘to
      ; right-inverse-of = to∘from
      }
    }
    where

    from∘to : ∀ {xs} (p : Any P xs ⊎ Any Q xs) → Any-⊎⁻ (Any-⊎⁺ p) ≡ p
    from∘to (inj₁ (here  p)) = P.refl
    from∘to (inj₁ (there p)) rewrite from∘to (inj₁ p) = P.refl
    from∘to (inj₂ (here  q)) = P.refl
    from∘to (inj₂ (there q)) rewrite from∘to (inj₂ q) = P.refl

    to∘from : ∀ {xs} (p : Any (λ x → P x ⊎ Q x) xs) →
              Any-⊎⁺ (Any-⊎⁻ p) ≡ p
    to∘from (here (inj₁ p)) = P.refl
    to∘from (here (inj₂ q)) = P.refl
    to∘from (there p) with Any-⊎⁻ p | to∘from p
    to∘from (there .(Any.map inj₁ p)) | inj₁ p | P.refl = P.refl
    to∘from (there .(Any.map inj₂ q)) | inj₂ q | P.refl = P.refl

------------------------------------------------------------------------
-- Products "commute" with Any.

module _ {a b p q} {A : Set a} {B : Set b}
         {P : Pred A p} {Q : Pred B q} where

  Any-×⁺ : ∀ {xs ys} → Any P xs × Any Q ys →
           Any (λ x → Any (λ y → P x × Q y) ys) xs
  Any-×⁺ (p , q) = Any.map (λ p → Any.map (λ q → (p , q)) q) p

  Any-×⁻ : ∀ {xs ys} → Any (λ x → Any (λ y → P x × Q y) ys) xs →
           Any P xs × Any Q ys
  Any-×⁻ pq with Prod.map id (Prod.map id find) (find pq)
  ... | (x , x∈xs , y , y∈ys , p , q) = (lose x∈xs p , lose y∈ys q)

  ×↔ : ∀ {xs ys} →
       (Any P xs × Any Q ys) ↔ Any (λ x → Any (λ y → P x × Q y) ys) xs
  ×↔ {xs} {ys} = record
    { to         = P.→-to-⟶ Any-×⁺
    ; from       = P.→-to-⟶ Any-×⁻
    ; inverse-of = record
      { left-inverse-of  = from∘to
      ; right-inverse-of = to∘from
      }
    }
    where
    from∘to : ∀ pq → Any-×⁻ (Any-×⁺ pq) ≡ pq
    from∘to (p , q)
      rewrite find∘map {Q = λ x → Any (λ y → P x × Q y) ys}
                       p (λ p → Any.map (λ q → (p , q)) q)
              | find∘map {Q = λ y → P (proj₁ (find p)) × Q y}
                         q (λ q → proj₂ (proj₂ (find p)) , q)
              | lose∘find p
            | lose∘find q
            = refl

    to∘from : ∀ pq → Any-×⁺ (Any-×⁻ pq) ≡ pq
    to∘from pq
      with find pq
        | (λ (f : (proj₁ (find pq) ≡_) ⋐ _) → map∘find pq {f})
    ... | (x , x∈xs , pq′) | lem₁
      with find pq′
        | (λ (f : (proj₁ (find pq′) ≡_) ⋐ _) → map∘find pq′ {f})
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
------------------------------------------------------------------------
-- map

module _ {a b} {A : Set a} {B : Set b} where

  map⁺ : ∀ {p} {P : B → Set p} {f : A → B} {xs} →
         Any (P ∘ f) xs → Any P (List.map f xs)
  map⁺ (here p)  = here p
  map⁺ (there p) = there $ map⁺ p

  map⁻ : ∀ {p} {P : B → Set p} {f : A → B} {xs} →
         Any P (List.map f xs) → Any (P ∘ f) xs
  map⁻ {xs = []}     ()
  map⁻ {xs = x ∷ xs} (here p)  = here p
  map⁻ {xs = x ∷ xs} (there p) = there $ map⁻ p

  map⁺∘map⁻ : ∀ {p} {P : B → Set p} {f : A → B} {xs} →
              (p : Any P (List.map f xs)) → map⁺ (map⁻ p) ≡ p
  map⁺∘map⁻ {xs = []}     ()
  map⁺∘map⁻ {xs = x ∷ xs} (here  p) = refl
  map⁺∘map⁻ {xs = x ∷ xs} (there p) = P.cong there (map⁺∘map⁻ p)

  map⁻∘map⁺ : ∀ {p} (P : B → Set p) {f : A → B} {xs} →
              (p : Any (P ∘ f) xs) → map⁻ {P = P} (map⁺ p) ≡ p
  map⁻∘map⁺ P (here  p) = refl
  map⁻∘map⁺ P (there p) = P.cong there (map⁻∘map⁺ P p)

  map↔ : ∀ {p} {P : B → Set p} {f : A → B} {xs} →
         Any (P ∘ f) xs ↔ Any P (List.map f xs)
  map↔ {P = P} {f = f} = record
    { to         = P.→-to-⟶ $ map⁺ {P = P} {f = f}
    ; from       = P.→-to-⟶ $ map⁻ {P = P} {f = f}
    ; inverse-of = record
      { left-inverse-of  = map⁻∘map⁺ P
      ; right-inverse-of = map⁺∘map⁻
      }
    }

------------------------------------------------------------------------
-- mapMaybe

module _ {a b p} {A : Set a} {B : Set b} {P : B → Set p}
         (f : A → Maybe B) where

  mapMaybe⁺ : ∀ xs → Any (Maybe.Any P) (map f xs) →
              Any P (mapMaybe f xs)
  mapMaybe⁺ []       ()
  mapMaybe⁺ (x ∷ xs) ps with f x | ps
  ... | nothing | here  ()
  ... | nothing | there pxs      = mapMaybe⁺ xs pxs
  ... | just _  | here (just py) = here py
  ... | just _  | there pxs      = there (mapMaybe⁺ xs pxs)

------------------------------------------------------------------------
-- _++_

module _ {a p} {A : Set a} {P : A → Set p} where

  ++⁺ˡ : ∀ {xs ys} → Any P xs → Any P (xs ++ ys)
  ++⁺ˡ (here p)  = here p
  ++⁺ˡ (there p) = there (++⁺ˡ p)

  ++⁺ʳ : ∀ xs {ys} → Any P ys → Any P (xs ++ ys)
  ++⁺ʳ []       p = p
  ++⁺ʳ (x ∷ xs) p = there (++⁺ʳ xs p)

  ++⁻ : ∀ xs {ys} → Any P (xs ++ ys) → Any P xs ⊎ Any P ys
  ++⁻ []       p         = inj₂ p
  ++⁻ (x ∷ xs) (here p)  = inj₁ (here p)
  ++⁻ (x ∷ xs) (there p) = Sum.map there id (++⁻ xs p)

  ++⁺∘++⁻ : ∀ xs {ys} (p : Any P (xs ++ ys)) →
            [ ++⁺ˡ , ++⁺ʳ xs ]′ (++⁻ xs p) ≡ p
  ++⁺∘++⁻ []       p         = refl
  ++⁺∘++⁻ (x ∷ xs) (here  p) = refl
  ++⁺∘++⁻ (x ∷ xs) (there p) with ++⁻ xs p | ++⁺∘++⁻ xs p
  ++⁺∘++⁻ (x ∷ xs) (there p) | inj₁ p′ | ih = P.cong there ih
  ++⁺∘++⁻ (x ∷ xs) (there p) | inj₂ p′ | ih = P.cong there ih

  ++⁻∘++⁺ : ∀ xs {ys} (p : Any P xs ⊎ Any P ys) →
            ++⁻ xs ([ ++⁺ˡ , ++⁺ʳ xs ]′ p) ≡ p
  ++⁻∘++⁺ []            (inj₁ ())
  ++⁻∘++⁺ []            (inj₂ p)         = refl
  ++⁻∘++⁺ (x ∷ xs)      (inj₁ (here  p)) = refl
  ++⁻∘++⁺ (x ∷ xs) {ys} (inj₁ (there p)) rewrite ++⁻∘++⁺ xs {ys} (inj₁ p) = refl
  ++⁻∘++⁺ (x ∷ xs)      (inj₂ p)         rewrite ++⁻∘++⁺ xs      (inj₂ p) = refl

  ++↔ : ∀ {xs ys} → (Any P xs ⊎ Any P ys) ↔ Any P (xs ++ ys)
  ++↔ {xs = xs} = record
    { to         = P.→-to-⟶ [ ++⁺ˡ , ++⁺ʳ xs ]′
    ; from       = P.→-to-⟶ $ ++⁻ xs
    ; inverse-of = record
      { left-inverse-of  = ++⁻∘++⁺ xs
      ; right-inverse-of = ++⁺∘++⁻ xs
      }
    }

  ++-comm : ∀ xs ys → Any P (xs ++ ys) → Any P (ys ++ xs)
  ++-comm xs ys = [ ++⁺ʳ ys , ++⁺ˡ ]′ ∘ ++⁻ xs

  ++-comm∘++-comm : ∀ xs {ys} (p : Any P (xs ++ ys)) →
                    ++-comm ys xs (++-comm xs ys p) ≡ p
  ++-comm∘++-comm [] {ys} p
    rewrite ++⁻∘++⁺ ys {ys = []} (inj₁ p) = P.refl
  ++-comm∘++-comm (x ∷ xs) {ys} (here p)
    rewrite ++⁻∘++⁺ ys {ys = x ∷ xs} (inj₂ (here p)) = P.refl
  ++-comm∘++-comm (x ∷ xs)      (there p) with ++⁻ xs p | ++-comm∘++-comm xs p
  ++-comm∘++-comm (x ∷ xs) {ys} (there .([ ++⁺ʳ xs , ++⁺ˡ ]′ (++⁻ ys (++⁺ʳ ys p))))
    | inj₁ p | P.refl
    rewrite ++⁻∘++⁺ ys (inj₂                 p)
            | ++⁻∘++⁺ ys (inj₂ $ there {x = x} p) = P.refl
  ++-comm∘++-comm (x ∷ xs) {ys} (there .([ ++⁺ʳ xs , ++⁺ˡ ]′ (++⁻ ys (++⁺ˡ p))))
    | inj₂ p | P.refl
    rewrite ++⁻∘++⁺ ys {ys =     xs} (inj₁ p)
            | ++⁻∘++⁺ ys {ys = x ∷ xs} (inj₁ p) = P.refl

  ++↔++ : ∀ xs ys → Any P (xs ++ ys) ↔ Any P (ys ++ xs)
  ++↔++ xs ys = record
    { to         = P.→-to-⟶ $ ++-comm xs ys
    ; from       = P.→-to-⟶ $ ++-comm ys xs
    ; inverse-of = record
      { left-inverse-of  = ++-comm∘++-comm xs
      ; right-inverse-of = ++-comm∘++-comm ys
      }
    }

------------------------------------------------------------------------
-- concat

module _ {a p} {A : Set a} {P : A → Set p} where

  concat⁺ : ∀ {xss} → Any (Any P) xss → Any P (concat xss)
  concat⁺ (here p)           = ++⁺ˡ p
  concat⁺ (there {x = xs} p) = ++⁺ʳ xs (concat⁺ p)

  concat⁻ : ∀ xss → Any P (concat xss) → Any (Any P) xss
  concat⁻ []               ()
  concat⁻ ([]       ∷ xss) p         = there $ concat⁻ xss p
  concat⁻ ((x ∷ xs) ∷ xss) (here  p) = here (here p)
  concat⁻ ((x ∷ xs) ∷ xss) (there p) with concat⁻ (xs ∷ xss) p
  ... | here  p′ = here (there p′)
  ... | there p′ = there p′

  concat⁻∘++⁺ˡ : ∀ {xs} xss (p : Any P xs) →
                 concat⁻ (xs ∷ xss) (++⁺ˡ p) ≡ here p
  concat⁻∘++⁺ˡ xss (here  p) = refl
  concat⁻∘++⁺ˡ xss (there p) rewrite concat⁻∘++⁺ˡ xss p = refl

  concat⁻∘++⁺ʳ : ∀ xs xss (p : Any P (concat xss)) →
                   concat⁻ (xs ∷ xss) (++⁺ʳ xs p) ≡ there (concat⁻ xss p)
  concat⁻∘++⁺ʳ []       xss p = refl
  concat⁻∘++⁺ʳ (x ∷ xs) xss p rewrite concat⁻∘++⁺ʳ xs xss p = refl

  concat⁺∘concat⁻ : ∀ xss (p : Any P (concat xss)) →
                      concat⁺ (concat⁻ xss p) ≡ p
  concat⁺∘concat⁻ []               ()
  concat⁺∘concat⁻ ([]       ∷ xss) p         = concat⁺∘concat⁻ xss p
  concat⁺∘concat⁻ ((x ∷ xs) ∷ xss) (here p)  = refl
  concat⁺∘concat⁻ ((x ∷ xs) ∷ xss) (there p)
                with concat⁻ (xs ∷ xss) p | concat⁺∘concat⁻ (xs ∷ xss) p
  concat⁺∘concat⁻ ((x ∷ xs) ∷ xss) (there .(++⁺ˡ p′))              | here  p′ | refl = refl
  concat⁺∘concat⁻ ((x ∷ xs) ∷ xss) (there .(++⁺ʳ xs (concat⁺ p′))) | there p′ | refl = refl

  concat⁻∘concat⁺ : ∀ {xss} (p : Any (Any P) xss) → concat⁻ xss (concat⁺ p) ≡ p
  concat⁻∘concat⁺ (here                      p) = concat⁻∘++⁺ˡ _ p
  concat⁻∘concat⁺ (there {x = xs} {xs = xss} p)
    rewrite concat⁻∘++⁺ʳ xs xss (concat⁺ p) =
      P.cong there $ concat⁻∘concat⁺ p

  concat↔ : ∀ {xss} → Any (Any P) xss ↔ Any P (concat xss)
  concat↔ {xss = xss} = record
    { to         = P.→-to-⟶ $ concat⁺
    ; from       = P.→-to-⟶ $ concat⁻ xss
    ; inverse-of = record
      { left-inverse-of  = concat⁻∘concat⁺
      ; right-inverse-of = concat⁺∘concat⁻ xss
      }
    }

------------------------------------------------------------------------
-- applyUpTo

module _ {a p} {A : Set a} {P : A → Set p} where

  applyUpTo⁺ : ∀ f {i n} → P (f i) → i < n → Any P (applyUpTo f n)
  applyUpTo⁺ _ p (s≤s z≤n)       = here p
  applyUpTo⁺ f p (s≤s (s≤s i<n)) =
    there (applyUpTo⁺ (f ∘ suc) p (s≤s i<n))

  applyUpTo⁻ : ∀ f {n} → Any P (applyUpTo f n) →
               ∃ λ i → i < n × P (f i)
  applyUpTo⁻ f {zero}  ()
  applyUpTo⁻ f {suc n} (here p)  = zero , s≤s z≤n , p
  applyUpTo⁻ f {suc n} (there p) with applyUpTo⁻ (f ∘ suc) p
  ... | i , i<n , q = suc i , s≤s i<n , q

------------------------------------------------------------------------
-- tabulate

module _ {a p} {A : Set a} {P : A → Set p} where

  tabulate⁺ : ∀ {n} {f : Fin n → A} i → P (f i) → Any P (tabulate f)
  tabulate⁺ fzero    p = here p
  tabulate⁺ (fsuc i) p = there (tabulate⁺ i p)

  tabulate⁻ : ∀ {n} {f : Fin n → A} →
              Any P (tabulate f) → ∃ λ i → P (f i)
  tabulate⁻ {zero}  ()
  tabulate⁻ {suc n} (here p)   = fzero , p
  tabulate⁻ {suc n} (there p) = Prod.map fsuc id (tabulate⁻ p)

------------------------------------------------------------------------
-- map-with-∈.

module _ {a b p} {A : Set a} {B : Set b} {P : B → Set p} where

  map-with-∈⁺ : ∀ {xs : List A} (f : ∀ {x} → x ∈ xs → B) →
                (∃₂ λ x (x∈xs : x ∈ xs) → P (f x∈xs)) →
                Any P (map-with-∈ xs f)
  map-with-∈⁺ f (_ , here refl  , p) = here p
  map-with-∈⁺ f (_ , there x∈xs , p) =
    there $ map-with-∈⁺ (f ∘ there) (_ , x∈xs , p)

  map-with-∈⁻ : ∀ (xs : List A) (f : ∀ {x} → x ∈ xs → B) →
                Any P (map-with-∈ xs f) →
                ∃₂ λ x (x∈xs : x ∈ xs) → P (f x∈xs)
  map-with-∈⁻ []       f ()
  map-with-∈⁻ (y ∷ xs) f (here  p) = (y , here refl , p)
  map-with-∈⁻ (y ∷ xs) f (there p) =
    Prod.map id (Prod.map there id) $ map-with-∈⁻ xs (f ∘ there) p

  map-with-∈↔ : ∀  {xs : List A} {f : ∀ {x} → x ∈ xs → B} →
    (∃₂ λ x (x∈xs : x ∈ xs) → P (f x∈xs)) ↔ Any P (map-with-∈ xs f)
  map-with-∈↔ = record
    { to         = P.→-to-⟶ (map-with-∈⁺ _)
    ; from       = P.→-to-⟶ (map-with-∈⁻ _ _)
    ; inverse-of = record
      { left-inverse-of  = from∘to _
      ; right-inverse-of = to∘from _ _
      }
    }
    where

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
-- return

module _ {a p} {A : Set a} {P : A → Set p} where

  return⁺ : ∀ {x} → P x → Any P (return x)
  return⁺ = here

  return⁻ : ∀ {x} → Any P (return x) → P x
  return⁻ (here p)   = p
  return⁻ (there ())

  return⁺∘return⁻ : ∀ {x} (p : Any P (return x)) →
                    return⁺ (return⁻ p) ≡ p
  return⁺∘return⁻ (here p)   = refl
  return⁺∘return⁻ (there ())

  return⁻∘return⁺ : ∀ {x} (p : P x) → return⁻ (return⁺ p) ≡ p
  return⁻∘return⁺ p = refl

  return↔ : ∀ {x} → P x ↔ Any P (return x)
  return↔ = record
    { to         = P.→-to-⟶ $ return⁺
    ; from       = P.→-to-⟶ $ return⁻
    ; inverse-of = record
      { left-inverse-of  = return⁻∘return⁺
      ; right-inverse-of = return⁺∘return⁻
      }
    }

------------------------------------------------------------------------
-- _∷_.

∷↔ : ∀ {a p} {A : Set a} (P : A → Set p) {x xs} →
     (P x ⊎ Any P xs) ↔ Any P (x ∷ xs)
∷↔ P {x} {xs} =
  (P x         ⊎ Any P xs)  ↔⟨ return↔ {P = P} ⊎-cong (Any P xs ∎) ⟩
  (Any P [ x ] ⊎ Any P xs)  ↔⟨ ++↔ {P = P} {xs = [ x ]} ⟩
  Any P (x ∷ xs)            ∎

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
