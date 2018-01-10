------------------------------------------------------------------------
-- The Agda standard library
--
-- Some Vec-related properties
------------------------------------------------------------------------

module Data.Vec.Properties where

open import Data.Empty using (⊥-elim)
open import Data.Fin as Fin using (Fin; zero; suc; toℕ; fromℕ)
open import Data.Fin.Properties using (_+′_)
open import Data.List.Any using (here; there)
import Data.List.Any.Membership.Propositional as List
open import Data.Nat
open import Data.Nat.Properties using (+-assoc)
open import Data.Product as Prod using (_×_; _,_; proj₁; proj₂; <_,_>)
open import Data.Vec
open import Function
open import Function.Inverse using (_↔_)
open import Relation.Binary

module UsingVectorEquality {s₁ s₂} (S : Setoid s₁ s₂) where

  private module SS = Setoid S
  open SS using () renaming (Carrier to A)
  import Data.Vec.Relation.Equality as VecEq
  open VecEq.Equality S

  replicate-lemma : ∀ {m} n x (xs : Vec A m) →
                    replicate {n = n}     x ++ (x ∷ xs) ≈
                    replicate {n = 1 + n} x ++      xs
  replicate-lemma zero    x xs = refl (x ∷ xs)
  replicate-lemma (suc n) x xs = SS.refl ∷-cong replicate-lemma n x xs

  xs++[]=xs : ∀ {n} (xs : Vec A n) → xs ++ [] ≈ xs
  xs++[]=xs []       = []-cong
  xs++[]=xs (x ∷ xs) = SS.refl ∷-cong xs++[]=xs xs

  map-++-commute : ∀ {b m n} {B : Set b}
                   (f : B → A) (xs : Vec B m) {ys : Vec B n} →
                   map f (xs ++ ys) ≈ map f xs ++ map f ys
  map-++-commute f []       = refl _
  map-++-commute f (x ∷ xs) = SS.refl ∷-cong map-++-commute f xs

open import Relation.Binary.PropositionalEquality as P
  using (_≡_; _≢_; refl; _≗_)
open import Relation.Binary.HeterogeneousEquality using (_≅_; refl)

------------------------------------------------------------------------
-- Properties of propositional equality over vectors

module _ {a} {A : Set a} {n} {x y : A} {xs ys : Vec A n} where

 ∷-injectiveˡ : x ∷ xs ≡ y ∷ ys → x ≡ y
 ∷-injectiveˡ refl = refl

 ∷-injectiveʳ : x ∷ xs ≡ y ∷ ys → xs ≡ ys
 ∷-injectiveʳ refl = refl

 ∷-injective : (x ∷ xs) ≡ (y ∷ ys) → x ≡ y × xs ≡ ys
 ∷-injective refl = refl , refl

------------------------------------------------------------------------
-- _[_]=_

module _ {a} {A : Set a} where

  []=-irrelevance : ∀ {n} {xs : Vec A n} {i x} →
                    (p q : xs [ i ]= x) → p ≡ q
  []=-irrelevance here            here             = refl
  []=-irrelevance (there xs[i]=x) (there xs[i]=x') =
    P.cong there ([]=-irrelevance xs[i]=x xs[i]=x')

------------------------------------------------------------------------
-- lookup

module _ {a} {A : Set a} where

  []=⇒lookup : ∀ {n} {x : A} {xs} {i : Fin n} →
               xs [ i ]= x → lookup i xs ≡ x
  []=⇒lookup here            = refl
  []=⇒lookup (there xs[i]=x) = []=⇒lookup xs[i]=x

  lookup⇒[]= : ∀ {n} (i : Fin n) {x : A} xs →
               lookup i xs ≡ x → xs [ i ]= x
  lookup⇒[]= zero    (_ ∷ _)  refl = here
  lookup⇒[]= (suc i) (_  ∷ xs) p    = there (lookup⇒[]= i xs p)

  []=↔lookup : ∀ {n i} {x} {xs : Vec A n} →
               xs [ i ]= x ↔ lookup i xs ≡ x
  []=↔lookup = record
    { to         = P.→-to-⟶ []=⇒lookup
    ; from       = P.→-to-⟶ (lookup⇒[]= _ _)
    ; inverse-of = record
      { left-inverse-of  = λ _ → []=-irrelevance _ _
      ; right-inverse-of = λ _ → P.≡-irrelevance _ _
      }
    }

------------------------------------------------------------------------
-- _[_]≔_ (update)

module _ {a} {A : Set a} where

  []≔-idempotent : ∀ {n} (xs : Vec A n) (i : Fin n) {x₁ x₂ : A} →
                   (xs [ i ]≔ x₁) [ i ]≔ x₂ ≡ xs [ i ]≔ x₂
  []≔-idempotent []       ()
  []≔-idempotent (x ∷ xs) zero    = refl
  []≔-idempotent (x ∷ xs) (suc i) = P.cong (x ∷_) ([]≔-idempotent xs i)

  []≔-commutes : ∀ {n} (xs : Vec A n) (i j : Fin n) {x y : A} → i ≢ j →
                 (xs [ i ]≔ x) [ j ]≔ y ≡ (xs [ j ]≔ y) [ i ]≔ x
  []≔-commutes []       ()      ()      _
  []≔-commutes (x ∷ xs) zero    zero    0≢0 = ⊥-elim $ 0≢0 refl
  []≔-commutes (x ∷ xs) zero    (suc i) _   = refl
  []≔-commutes (x ∷ xs) (suc i) zero    _   = refl
  []≔-commutes (x ∷ xs) (suc i) (suc j) i≢j =
    P.cong (x ∷_) $ []≔-commutes xs i j (i≢j ∘ P.cong suc)

  []≔-updates : ∀ {n} (xs : Vec A n) (i : Fin n) {x : A} →
                (xs [ i ]≔ x) [ i ]= x
  []≔-updates []       ()
  []≔-updates (x ∷ xs) zero    = here
  []≔-updates (x ∷ xs) (suc i) = there ([]≔-updates xs i)

  []≔-minimal : ∀ {n} (xs : Vec A n) (i j : Fin n) {x y : A} → i ≢ j →
                xs [ i ]= x → (xs [ j ]≔ y) [ i ]= x
  []≔-minimal []       ()      ()      _   _
  []≔-minimal (x ∷ xs) .zero   zero    0≢0 here        = ⊥-elim (0≢0 refl)
  []≔-minimal (x ∷ xs) .zero   (suc j) _   here        = here
  []≔-minimal (x ∷ xs) (suc i) zero    _   (there loc) = there loc
  []≔-minimal (x ∷ xs) (suc i) (suc j) i≢j (there loc) =
    there ([]≔-minimal xs i j (i≢j ∘ P.cong suc) loc)

  []≔-lookup : ∀ {n} (xs : Vec A n) (i : Fin n) →
               xs [ i ]≔ lookup i xs ≡ xs
  []≔-lookup []       ()
  []≔-lookup (x ∷ xs) zero    = refl
  []≔-lookup (x ∷ xs) (suc i) = P.cong (_∷_ x) $ []≔-lookup xs i

  lookup∘update : ∀ {n} (i : Fin n) (xs : Vec A n) x →
                  lookup i (xs [ i ]≔ x) ≡ x
  lookup∘update zero    (_ ∷ xs) x = refl
  lookup∘update (suc i) (_ ∷ xs) x = lookup∘update i xs x

  lookup∘update′ : ∀ {n} {i j : Fin n} → i ≢ j → ∀ (xs : Vec A n) y →
                   lookup i (xs [ j ]≔ y) ≡ lookup i xs
  lookup∘update′ {i = zero}  {zero}  i≢j      xs  y = ⊥-elim (i≢j refl)
  lookup∘update′ {i = zero}  {suc j} i≢j (x ∷ xs) y = refl
  lookup∘update′ {i = suc i} {zero}  i≢j (x ∷ xs) y = refl
  lookup∘update′ {i = suc i} {suc j} i≢j (x ∷ xs) y =
    lookup∘update′ (i≢j ∘ P.cong suc) xs y

------------------------------------------------------------------------
-- map

map-id : ∀ {a n} {A : Set a} → map {n = n} {A} id ≗ id
map-id []       = refl
map-id (x ∷ xs) = P.cong (x ∷_) (map-id xs)

map-cong : ∀ {a b n} {A : Set a} {B : Set b} {f g : A → B} →
           f ≗ g → map {n = n} f ≗ map g
map-cong f≗g []       = refl
map-cong f≗g (x ∷ xs) = P.cong₂ _∷_ (f≗g x) (map-cong f≗g xs)

map-∘ : ∀ {a b c n} {A : Set a} {B : Set b} {C : Set c}
        (f : B → C) (g : A → B) →
        map {n = n} (f ∘ g) ≗ map f ∘ map g
map-∘ f g []       = refl
map-∘ f g (x ∷ xs) = P.cong (f (g x) ∷_) (map-∘ f g xs)

lookup-map : ∀ {a b n} {A : Set a} {B : Set b}
             (i : Fin n) (f : A → B) (xs : Vec A n) →
             lookup i (map f xs) ≡ f (lookup i xs)
lookup-map zero    f (x ∷ xs) = refl
lookup-map (suc i) f (x ∷ xs) = lookup-map i f xs

map-[]≔ : ∀ {n a b} {A : Set a} {B : Set b}
          (f : A → B) (xs : Vec A n) (i : Fin n) {x : A} →
          map f (xs [ i ]≔ x) ≡ map f xs [ i ]≔ f x
map-[]≔ f []       ()
map-[]≔ f (x ∷ xs) zero    = refl
map-[]≔ f (x ∷ xs) (suc i) = P.cong (_ ∷_) $ map-[]≔ f xs i

------------------------------------------------------------------------
-- _++_

module _ {a} {A : Set a} where

  lookup-++-< : ∀ {m n} (xs : Vec A m) (ys : Vec A n) →
                ∀ i (i<m : toℕ i < m) →
                lookup i (xs ++ ys) ≡ lookup (Fin.fromℕ≤ i<m) xs
  lookup-++-< []       ys i       ()
  lookup-++-< (x ∷ xs) ys zero    (s≤s z≤n)       = refl
  lookup-++-< (x ∷ xs) ys (suc i) (s≤s (s≤s i<m)) =
    lookup-++-< xs ys i (s≤s i<m)

  lookup-++-≥ : ∀ {m n} (xs : Vec A m) (ys : Vec A n) →
                ∀ i (i≥m : toℕ i ≥ m) →
                lookup i (xs ++ ys) ≡ lookup (Fin.reduce≥ i i≥m) ys
  lookup-++-≥ []       ys i       i≥m       = refl
  lookup-++-≥ (x ∷ xs) ys zero    ()
  lookup-++-≥ (x ∷ xs) ys (suc i) (s≤s i≥m) = lookup-++-≥ xs ys i i≥m

  lookup-++-inject+ : ∀ {m n} (xs : Vec A m) (ys : Vec A n) i →
                      lookup (Fin.inject+ n i) (xs ++ ys) ≡ lookup i xs
  lookup-++-inject+ []       ys ()
  lookup-++-inject+ (x ∷ xs) ys zero    = refl
  lookup-++-inject+ (x ∷ xs) ys (suc i) = lookup-++-inject+ xs ys i

  lookup-++-+′ : ∀ {m n} (xs : Vec A m) (ys : Vec A n) i →
                 lookup (fromℕ m +′ i) (xs ++ ys) ≡ lookup i ys
  lookup-++-+′ []       ys       zero    = refl
  lookup-++-+′ []       (y ∷ xs) (suc i) = lookup-++-+′ [] xs i
  lookup-++-+′ (x ∷ xs) ys       i       = lookup-++-+′ xs ys i

  []≔-++-inject+ : ∀ {m n x} (xs : Vec A m) (ys : Vec A n) i →
                   (xs ++ ys) [ Fin.inject+ n i ]≔ x ≡ (xs [ i ]≔ x) ++ ys
  []≔-++-inject+ []       ys ()
  []≔-++-inject+ (x ∷ xs) ys zero    = refl
  []≔-++-inject+ (x ∷ xs) ys (suc i) =
    P.cong (x ∷_) $ []≔-++-inject+ xs ys i

------------------------------------------------------------------------
-- zipWith

module _ {a b c d} {A : Set a} {B : Set b} {C : Set c} {D : Set d} where

  zipWith-map₁ : ∀ {n} (_⊕_ : B → C → D) (f : A → B)
                 (xs : Vec A n) (ys : Vec C n) →
                 zipWith _⊕_ (map f xs) ys ≡ zipWith (λ x y → f x ⊕ y) xs ys
  zipWith-map₁ _⊕_ f [] [] = refl
  zipWith-map₁ _⊕_ f (x ∷ xs) (y ∷ ys) =
    P.cong (f x ⊕ y ∷_) (zipWith-map₁ _⊕_ f xs ys)

  zipWith-map₂ : ∀ {n} (_⊕_ : A → C → D) (f : B → C)
                 (xs : Vec A n) (ys : Vec B n) →
                 zipWith _⊕_ xs (map f ys) ≡ zipWith (λ x y → x ⊕ f y) xs ys
  zipWith-map₂ _⊕_ f [] [] = refl
  zipWith-map₂ _⊕_ f (x ∷ xs) (y ∷ ys) =
    P.cong (x ⊕ f y ∷_) (zipWith-map₂ _⊕_ f xs ys)

------------------------------------------------------------------------
-- zip

module _ {a b} {A : Set a} {B : Set b} where


  lookup-zip : ∀ {n} (i : Fin n) (xs : Vec A n) (ys : Vec B n) →
               lookup i (zip xs ys) ≡ (lookup i xs , lookup i ys)
  lookup-zip zero    (x ∷ xs) (y ∷ ys) = refl
  lookup-zip (suc i) (x ∷ xs) (y ∷ ys) = lookup-zip i xs ys

  -- map lifts projections to vectors of products.

  map-proj₁-zip : ∀ {n} (xs : Vec A n) (ys : Vec B n) →
                  map proj₁ (zip xs ys) ≡ xs
  map-proj₁-zip []       []       = refl
  map-proj₁-zip (x ∷ xs) (y ∷ ys) = P.cong (x ∷_) (map-proj₁-zip xs ys)

  map-proj₂-zip : ∀ {n} (xs : Vec A n) (ys : Vec B n) →
                  map proj₂ (zip xs ys) ≡ ys
  map-proj₂-zip []       []       = refl
  map-proj₂-zip (x ∷ xs) (y ∷ ys) = P.cong (y ∷_) (map-proj₂-zip xs ys)

-- map lifts pairing to vectors of products.

map-<,>-zip : ∀ {a b c n} {A : Set a} {B : Set b} {C : Set c}
              (f : A → B) (g : A → C) (xs : Vec A n) →
              map < f , g > xs ≡ zip (map f xs) (map g xs)
map-<,>-zip f g []       = P.refl
map-<,>-zip f g (x ∷ xs) = P.cong (_ ∷_) (map-<,>-zip f g xs)

map-zip : ∀ {a b c d n} {A : Set a} {B : Set b} {C : Set c} {D : Set d}
          (f : A → B) (g : C → D) (xs : Vec A n) (ys : Vec C n) →
          map (Prod.map f g) (zip xs ys) ≡ zip (map f xs) (map g ys)
map-zip f g []       []       = refl
map-zip f g (x ∷ xs) (y ∷ ys) = P.cong (_ ∷_) (map-zip f g xs ys)

------------------------------------------------------------------------
-- unzip

module _ {a b} {A : Set a} {B : Set b} where

  lookup-unzip : ∀ {n} (i : Fin n) (xys : Vec (A × B) n) →
                 let xs , ys = unzip xys
                 in (lookup i xs , lookup i ys) ≡ lookup i xys
  lookup-unzip ()      []
  lookup-unzip zero    ((x , y) ∷ xys) = refl
  lookup-unzip (suc i) ((x , y) ∷ xys) = lookup-unzip i xys

  map-unzip : ∀ {c d n} {C : Set c} {D : Set d}
              (f : A → B) (g : C → D) (xys : Vec (A × C) n) →
              let xs , ys = unzip xys
              in (map f xs , map g ys) ≡ unzip (map (Prod.map f g) xys)
  map-unzip f g []              = refl
  map-unzip f g ((x , y) ∷ xys) =
    P.cong (Prod.map (f x ∷_) (g y ∷_)) (map-unzip f g xys)

  -- Products of vectors are isomorphic to vectors of products.

  unzip∘zip : ∀ {n} (xs : Vec A n) (ys : Vec B n) →
              unzip (zip xs ys) ≡ (xs , ys)
  unzip∘zip [] []             = refl
  unzip∘zip (x ∷ xs) (y ∷ ys) =
    P.cong (Prod.map (x ∷_) (y ∷_)) (unzip∘zip xs ys)

  zip∘unzip : ∀ {n} (xys : Vec (A × B) n) →
              (Prod.uncurry zip) (unzip xys) ≡ xys
  zip∘unzip []              = refl
  zip∘unzip ((x , y) ∷ xys) = P.cong ((x , y) ∷_) (zip∘unzip xys)

  ×v↔v× : ∀ {n} → (Vec A n × Vec B n) ↔ Vec (A × B) n
  ×v↔v× = record
    { to         = P.→-to-⟶ (Prod.uncurry zip)
    ; from       = P.→-to-⟶ unzip
    ; inverse-of = record
      { left-inverse-of  = Prod.uncurry unzip∘zip
      ; right-inverse-of = zip∘unzip
      }
    }

------------------------------------------------------------------------
-- _⊛_

module _ {a b} {A : Set a} {B : Set b} where

  lookup-⊛ : ∀ {n} i (fs : Vec (A → B) n) (xs : Vec A n) →
             lookup i (fs ⊛ xs) ≡ (lookup i fs $ lookup i xs)
  lookup-⊛ zero    (f ∷ fs) (x ∷ xs) = refl
  lookup-⊛ (suc i) (f ∷ fs) (x ∷ xs) = lookup-⊛ i fs xs

  map-is-⊛ : ∀ {n} (f : A → B) (xs : Vec A n) →
             map f xs ≡ (replicate f ⊛ xs)
  map-is-⊛ f []       = refl
  map-is-⊛ f (x ∷ xs) = P.cong (_ ∷_) (map-is-⊛ f xs)

  ⊛-is-zipWith : ∀ {n} (fs : Vec (A → B) n) (xs : Vec A n) →
                 (fs ⊛ xs) ≡ zipWith _$_ fs xs
  ⊛-is-zipWith []       []       = refl
  ⊛-is-zipWith (f ∷ fs) (x ∷ xs) = P.cong (f x ∷_) (⊛-is-zipWith fs xs)

  zipWith-is-⊛ : ∀ {c} {C : Set c} {n} (f : A → B → C) →
                 (xs : Vec A n) (ys : Vec B n) →
                 zipWith f xs ys ≡ (replicate f ⊛ xs ⊛ ys)
  zipWith-is-⊛ f []       []       = refl
  zipWith-is-⊛ f (x ∷ xs) (y ∷ ys) = P.cong (_ ∷_) (zipWith-is-⊛ f xs ys)

------------------------------------------------------------------------
-- foldr

foldr-cong : ∀ {a b} {A : Set a}
             {B : ℕ → Set b} {f : ∀ {n} → A → B n → B (suc n)} {d}
             {C : ℕ → Set b} {g : ∀ {n} → A → C n → C (suc n)} {e} →
             (∀ {n x} {y : B n} {z : C n} → y ≅ z → f x y ≅ g x z) →
             d ≅ e → ∀ {n} (xs : Vec A n) →
             foldr B f d xs ≅ foldr C g e xs
foldr-cong _   d≅e []       = d≅e
foldr-cong f≅g d≅e (x ∷ xs) = f≅g (foldr-cong f≅g d≅e xs)

-- The (uniqueness part of the) universality property for foldr.

foldr-universal : ∀ {a b} {A : Set a} (B : ℕ → Set b)
                  (f : ∀ {n} → A → B n → B (suc n)) {e}
                  (h : ∀ {n} → Vec A n → B n) →
                  h [] ≡ e →
                  (∀ {n} x → h ∘ (x ∷_) ≗ f {n} x ∘ h) →
                  ∀ {n} → h ≗ foldr B {n} f e
foldr-universal B f {_} h base step []       = base
foldr-universal B f {e} h base step (x ∷ xs) = begin
  h (x ∷ xs)
    ≡⟨ step x xs ⟩
  f x (h xs)
    ≡⟨ P.cong (f x) (foldr-universal B f h base step xs) ⟩
  f x (foldr B f e xs)
    ∎
  where open P.≡-Reasoning

foldr-fusion : ∀ {a b c} {A : Set a}
               {B : ℕ → Set b} {f : ∀ {n} → A → B n → B (suc n)} e
               {C : ℕ → Set c} {g : ∀ {n} → A → C n → C (suc n)}
               (h : ∀ {n} → B n → C n) →
               (∀ {n} x → h ∘ f {n} x ≗ g x ∘ h) →
               ∀ {n} → h ∘ foldr B {n} f e ≗ foldr C g (h e)
foldr-fusion {B = B} {f} e {C} h fuse =
  foldr-universal C _ _ refl (λ x xs → fuse x (foldr B f e xs))

idIsFold : ∀ {a n} {A : Set a} → id ≗ foldr (Vec A) {n} _∷_ []
idIsFold = foldr-universal _ _ id refl (λ _ _ → refl)

------------------------------------------------------------------------
-- foldl

foldl-cong : ∀ {a b} {A : Set a}
             {B : ℕ → Set b} {f : ∀ {n} → B n → A → B (suc n)} {d}
             {C : ℕ → Set b} {g : ∀ {n} → C n → A → C (suc n)} {e} →
             (∀ {n x} {y : B n} {z : C n} → y ≅ z → f y x ≅ g z x) →
             d ≅ e → ∀ {n} (xs : Vec A n) →
             foldl B f d xs ≅ foldl C g e xs
foldl-cong _   d≅e []       = d≅e
foldl-cong f≅g d≅e (x ∷ xs) = foldl-cong f≅g (f≅g d≅e) xs

------------------------------------------------------------------------
-- sum

sum-++-commute : ∀ {m n} (xs : Vec ℕ m) {ys : Vec ℕ n} →
                 sum (xs ++ ys) ≡ sum xs + sum ys
sum-++-commute []       {_}  = refl
sum-++-commute (x ∷ xs) {ys} = begin
  x + sum (xs ++ ys)     ≡⟨ P.cong (x +_) (sum-++-commute xs) ⟩
  x + (sum xs + sum ys)  ≡⟨ P.sym (+-assoc x (sum xs) (sum ys)) ⟩
  sum (x ∷ xs) + sum ys  ∎
  where open P.≡-Reasoning

------------------------------------------------------------------------
-- replicate

lookup-replicate : ∀ {a n} {A : Set a} (i : Fin n) (x : A) →
                   lookup i (replicate x) ≡ x
lookup-replicate zero    = λ _ → refl
lookup-replicate (suc i) = lookup-replicate i

map-replicate :  ∀ {a b} {A : Set a} {B : Set b} (f : A → B) (x : A) →
                 ∀ n → map f (replicate x) ≡ replicate {n = n} (f x)
map-replicate f x zero = refl
map-replicate f x (suc n) = P.cong (f x ∷_) (map-replicate f x n)

module _ {a b c} {A : Set a} {B : Set b} {C : Set c} where

  zipWith-replicate₁ : ∀ {n} (_⊕_ : A → B → C) (x : A) (ys : Vec B n) →
                     zipWith _⊕_ (replicate x) ys ≡ map (x ⊕_) ys
  zipWith-replicate₁ _⊕_ x []       = refl
  zipWith-replicate₁ _⊕_ x (y ∷ ys) =
    P.cong (x ⊕ y ∷_) (zipWith-replicate₁ _⊕_ x ys)

  zipWith-replicate₂ : ∀ {n} (_⊕_ : A → B → C) (xs : Vec A n) (y : B) →
                     zipWith _⊕_ xs (replicate y) ≡ map (_⊕ y) xs
  zipWith-replicate₂ _⊕_ []       y = refl
  zipWith-replicate₂ _⊕_ (x ∷ xs) y =
    P.cong (x ⊕ y ∷_) (zipWith-replicate₂ _⊕_ xs y)

------------------------------------------------------------------------
-- tabulate

lookup∘tabulate : ∀ {a n} {A : Set a} (f : Fin n → A) (i : Fin n) →
                  lookup i (tabulate f) ≡ f i
lookup∘tabulate f zero    = refl
lookup∘tabulate f (suc i) = lookup∘tabulate (f ∘ suc) i

tabulate∘lookup : ∀ {a n} {A : Set a} (xs : Vec A n) →
                  tabulate (flip lookup xs) ≡ xs
tabulate∘lookup []       = refl
tabulate∘lookup (x ∷ xs) = P.cong (x ∷_) (tabulate∘lookup xs)

tabulate-∘ : ∀ {n a b} {A : Set a} {B : Set b}
             (f : A → B) (g : Fin n → A) →
             tabulate (f ∘ g) ≡ map f (tabulate g)
tabulate-∘ {zero}  f g = refl
tabulate-∘ {suc n} f g = P.cong (f (g zero) ∷_) (tabulate-∘ f (g ∘ suc))

------------------------------------------------------------------------
-- allFin

lookup-allFin : ∀ {n} (i : Fin n) → lookup i (allFin n) ≡ i
lookup-allFin = lookup∘tabulate id

allFin-map : ∀ n → allFin (suc n) ≡ zero ∷ map suc (allFin n)
allFin-map n = P.cong (zero ∷_) $ tabulate-∘ suc id

tabulate-allFin : ∀ {n a} {A : Set a} (f : Fin n → A) →
                  tabulate f ≡ map f (allFin n)
tabulate-allFin f = tabulate-∘ f id

-- If you look up every possible index, in increasing order, then you
-- get back the vector you started with.

map-lookup-allFin : ∀ {a} {A : Set a} {n} (xs : Vec A n) →
                    map (λ x → lookup x xs) (allFin n) ≡ xs
map-lookup-allFin {n = n} xs = begin
  map (λ x → lookup x xs) (allFin n) ≡⟨ P.sym $ tabulate-∘ (λ x → lookup x xs) id ⟩
  tabulate (λ x → lookup x xs)       ≡⟨ tabulate∘lookup xs ⟩
  xs                                 ∎
  where open P.≡-Reasoning

------------------------------------------------------------------------
-- Properties of _∈_

∈-++ₗ : ∀ {a m n} {A : Set a} {x : A} {xs : Vec A m} {ys : Vec A n} →
        x ∈ xs → x ∈ xs ++ ys
∈-++ₗ here         = here
∈-++ₗ (there x∈xs) = there (∈-++ₗ x∈xs)

∈-++ᵣ : ∀ {a m n} {A : Set a} {x : A} (xs : Vec A m) {ys : Vec A n} →
        x ∈ ys → x ∈ xs ++ ys
∈-++ᵣ []       x∈ys = x∈ys
∈-++ᵣ (x ∷ xs) x∈ys = there (∈-++ᵣ xs x∈ys)

∈-map : ∀ {a b m} {A : Set a} {B : Set b} {x : A} {xs : Vec A m}
        (f : A → B) → x ∈ xs → f x ∈ map f xs
∈-map f here         = here
∈-map f (there x∈xs) = there (∈-map f x∈xs)

∈-tabulate : ∀ {n a} {A : Set a} (f : Fin n → A) i → f i ∈ tabulate f
∈-tabulate f zero    = here
∈-tabulate f (suc i) = there (∈-tabulate (f ∘ suc) i)

∈-allFin : ∀ {n} (i : Fin n) → i ∈ allFin n
∈-allFin = ∈-tabulate id

∈-allPairs : ∀ {a b} {A : Set a} {B : Set b} {m n : ℕ}
             {xs : Vec A m} {ys : Vec B n}
             {x y} → x ∈ xs → y ∈ ys → (x , y) ∈ allPairs xs ys
∈-allPairs {xs = x ∷ xs} {ys} here         y∈ys =
  ∈-++ₗ (∈-map (x ,_) y∈ys)
∈-allPairs {xs = x ∷ xs} {ys} (there x∈xs) y∈ys =
  ∈-++ᵣ (map (x ,_) ys) (∈-allPairs x∈xs y∈ys)

∈⇒List-∈ : ∀ {a} {A : Set a} {n x} {xs : Vec A n} →
           x ∈ xs → x List.∈ toList xs
∈⇒List-∈ here       = here P.refl
∈⇒List-∈ (there x∈) = there (∈⇒List-∈ x∈)

List-∈⇒∈ : ∀ {a} {A : Set a} {x : A} {xs} →
           x List.∈ xs → x ∈ fromList xs
List-∈⇒∈ (here P.refl) = here
List-∈⇒∈ (there x∈)    = there (List-∈⇒∈ x∈)

------------------------------------------------------------------------
-- DEPRECATED NAMES
------------------------------------------------------------------------
-- Please use the new names as continuing support for the old names is
-- not guaranteed.

proof-irrelevance-[]= = []=-irrelevance
