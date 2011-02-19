------------------------------------------------------------------------
-- Some Vec-related properties
------------------------------------------------------------------------

{-# OPTIONS --universe-polymorphism #-}

module Data.Vec.Properties where

open import Algebra
open import Category.Applicative.Indexed
open import Category.Monad
open import Category.Monad.Identity
open import Data.Vec
open import Data.Nat
import Data.Nat.Properties as Nat
open import Data.Fin as Fin using (Fin; zero; suc; toℕ; fromℕ)
open import Data.Fin.Props using (_+′_)
open import Function
open import Function.Inverse using (_⇿_)
open import Level
open import Relation.Binary

module UsingVectorEquality {s₁ s₂} (S : Setoid s₁ s₂) where

  private module SS = Setoid S
  open SS using () renaming (Carrier to A)
  import Data.Vec.Equality as VecEq
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

open import Relation.Binary.PropositionalEquality as PropEq
open import Relation.Binary.HeterogeneousEquality as HetEq

-- lookup is an applicative functor morphism.

lookup-morphism :
  ∀ {a n} (i : Fin n) →
  Morphism (applicative {a = a})
           (RawMonad.rawIApplicative IdentityMonad)
lookup-morphism i = record
  { op      = lookup i
  ; op-pure = lookup-replicate i
  ; op-⊛    = lookup-⊛ i
  }
  where
  lookup-replicate : ∀ {a n} {A : Set a} (i : Fin n) →
                     lookup i ∘ replicate {A = A} ≗ id {A = A}
  lookup-replicate zero    = λ _ → refl
  lookup-replicate (suc i) = lookup-replicate i

  lookup-⊛ : ∀ {a b n} {A : Set a} {B : Set b}
             i (fs : Vec (A → B) n) (xs : Vec A n) →
             lookup i (fs ⊛ xs) ≡ (lookup i fs $ lookup i xs)
  lookup-⊛ zero    (f ∷ fs) (x ∷ xs) = refl
  lookup-⊛ (suc i) (f ∷ fs) (x ∷ xs) = lookup-⊛ i fs xs

-- tabulate is an inverse of flip lookup.

lookup∘tabulate : ∀ {a n} {A : Set a} (f : Fin n → A) (i : Fin n) →
                  lookup i (tabulate f) ≡ f i
lookup∘tabulate f zero    = refl
lookup∘tabulate f (suc i) = lookup∘tabulate (f ∘ suc) i

tabulate∘lookup : ∀ {a n} {A : Set a} (xs : Vec A n) →
                  tabulate (flip lookup xs) ≡ xs
tabulate∘lookup []       = refl
tabulate∘lookup (x ∷ xs) = PropEq.cong (_∷_ x) $ tabulate∘lookup xs

-- If you look up an index in allFin n, then you get the index.

lookup-allFin : ∀ {n} (i : Fin n) → lookup i (allFin n) ≡ i
lookup-allFin = lookup∘tabulate id

-- Various lemmas relating lookup and _++_.

lookup-++-< : ∀ {a} {A : Set a} {m n}
              (xs : Vec A m) (ys : Vec A n) i (i<m : toℕ i < m) →
              lookup i (xs ++ ys) ≡ lookup (Fin.fromℕ≤ i<m) xs
lookup-++-< []       ys i       ()
lookup-++-< (x ∷ xs) ys zero    (s≤s z≤n)       = refl
lookup-++-< (x ∷ xs) ys (suc i) (s≤s (s≤s i<m)) =
  lookup-++-< xs ys i (s≤s i<m)

lookup-++-≥ : ∀ {a} {A : Set a} {m n}
              (xs : Vec A m) (ys : Vec A n) i (i≥m : toℕ i ≥ m) →
              lookup i (xs ++ ys) ≡ lookup (Fin.reduce≥ i i≥m) ys
lookup-++-≥ []       ys i       i≥m = refl
lookup-++-≥ (x ∷ xs) ys zero    ()
lookup-++-≥ (x ∷ xs) ys (suc i) (s≤s i≥m) = lookup-++-≥ xs ys i i≥m

lookup-++-inject+ : ∀ {a} {A : Set a} {m n}
                    (xs : Vec A m) (ys : Vec A n) i →
                    lookup (Fin.inject+ n i) (xs ++ ys) ≡ lookup i xs
lookup-++-inject+ []       ys ()
lookup-++-inject+ (x ∷ xs) ys zero    = refl
lookup-++-inject+ (x ∷ xs) ys (suc i) = lookup-++-inject+ xs ys i

lookup-++-+′ : ∀ {a} {A : Set a} {m n}
               (xs : Vec A m) (ys : Vec A n) i →
               lookup (fromℕ m +′ i) (xs ++ ys) ≡ lookup i ys
lookup-++-+′ []       ys       zero    = refl
lookup-++-+′ []       (y ∷ xs) (suc i) = lookup-++-+′ [] xs i
lookup-++-+′ (x ∷ xs) ys       i       = lookup-++-+′ xs ys i

-- map is a congruence.

map-cong : ∀ {a b n} {A : Set a} {B : Set b} {f g : A → B} →
           f ≗ g → _≗_ {A = Vec A n} (map f) (map g)
map-cong f≗g []       = refl
map-cong f≗g (x ∷ xs) = PropEq.cong₂ _∷_ (f≗g x) (map-cong f≗g xs)

-- map is functorial.

map-id : ∀ {a n} {A : Set a} → _≗_ {A = Vec A n} (map id) id
map-id []       = refl
map-id (x ∷ xs) = PropEq.cong (_∷_ x) (map-id xs)

map-∘ : ∀ {a b c n} {A : Set a} {B : Set b} {C : Set c}
        (f : B → C) (g : A → B) →
        _≗_ {A = Vec A n} (map (f ∘ g)) (map f ∘ map g)
map-∘ f g []       = refl
map-∘ f g (x ∷ xs) = PropEq.cong (_∷_ (f (g x))) (map-∘ f g xs)

-- tabulate can be expressed using map and allFin.

tabulate-∘ : ∀ {n a b} {A : Set a} {B : Set b}
             (f : A → B) (g : Fin n → A) →
             tabulate (f ∘ g) ≡ map f (tabulate g)
tabulate-∘ {zero}  f g = refl
tabulate-∘ {suc n} f g =
  PropEq.cong (_∷_ (f (g zero))) (tabulate-∘ f (g ∘ suc))

tabulate-allFin : ∀ {n a} {A : Set a} (f : Fin n → A) →
                  tabulate f ≡ map f (allFin n)
tabulate-allFin f = tabulate-∘ f id

-- The positive case of allFin can be expressed recursively using map.

allFin-map : ∀ n → allFin (suc n) ≡ zero ∷ map suc (allFin n)
allFin-map n = PropEq.cong (_∷_ zero) $ tabulate-∘ suc id

-- If you look up every possible index, in increasing order, then you
-- get back the vector you started with.

map-lookup-allFin : ∀ {a} {A : Set a} {n} (xs : Vec A n) →
                    map (λ x → lookup x xs) (allFin n) ≡ xs
map-lookup-allFin {n = n} xs = begin
  map (λ x → lookup x xs) (allFin n) ≡⟨ PropEq.sym $ tabulate-∘ (λ x → lookup x xs) id ⟩
  tabulate (λ x → lookup x xs)       ≡⟨ tabulate∘lookup xs ⟩
  xs                                 ∎
  where open ≡-Reasoning

-- sum commutes with _++_.

sum-++-commute : ∀ {m n} (xs : Vec ℕ m) {ys : Vec ℕ n} →
                 sum (xs ++ ys) ≡ sum xs + sum ys
sum-++-commute []            = refl
sum-++-commute (x ∷ xs) {ys} = begin
  x + sum (xs ++ ys)
    ≡⟨ PropEq.cong (λ p → x + p) (sum-++-commute xs) ⟩
  x + (sum xs + sum ys)
    ≡⟨ PropEq.sym (+-assoc x (sum xs) (sum ys)) ⟩
  sum (x ∷ xs) + sum ys
    ∎
  where
  open ≡-Reasoning
  open CommutativeSemiring Nat.commutativeSemiring hiding (_+_; sym)

-- foldr is a congruence.

foldr-cong : ∀ {a} {A : Set a}
               {b₁} {B₁ : ℕ → Set b₁}
               {f₁ : ∀ {n} → A → B₁ n → B₁ (suc n)} {e₁}
               {b₂} {B₂ : ℕ → Set b₂}
               {f₂ : ∀ {n} → A → B₂ n → B₂ (suc n)} {e₂} →
             (∀ {n x} {y₁ : B₁ n} {y₂ : B₂ n} →
                y₁ ≅ y₂ → f₁ x y₁ ≅ f₂ x y₂) →
             e₁ ≅ e₂ →
             ∀ {n} (xs : Vec A n) →
             foldr B₁ f₁ e₁ xs ≅ foldr B₂ f₂ e₂ xs
foldr-cong           _     e₁=e₂ []       = e₁=e₂
foldr-cong {B₁ = B₁} f₁=f₂ e₁=e₂ (x ∷ xs) =
  f₁=f₂ (foldr-cong {B₁ = B₁} f₁=f₂ e₁=e₂ xs)

-- foldl is a congruence.

foldl-cong : ∀ {a} {A : Set a}
               {b₁} {B₁ : ℕ → Set b₁}
               {f₁ : ∀ {n} → B₁ n → A → B₁ (suc n)} {e₁}
               {b₂} {B₂ : ℕ → Set b₂}
               {f₂ : ∀ {n} → B₂ n → A → B₂ (suc n)} {e₂} →
             (∀ {n x} {y₁ : B₁ n} {y₂ : B₂ n} →
                y₁ ≅ y₂ → f₁ y₁ x ≅ f₂ y₂ x) →
             e₁ ≅ e₂ →
             ∀ {n} (xs : Vec A n) →
             foldl B₁ f₁ e₁ xs ≅ foldl B₂ f₂ e₂ xs
foldl-cong           _     e₁=e₂ []       = e₁=e₂
foldl-cong {B₁ = B₁} f₁=f₂ e₁=e₂ (x ∷ xs) =
  foldl-cong {B₁ = B₁ ∘ suc} f₁=f₂ (f₁=f₂ e₁=e₂) xs

-- The (uniqueness part of the) universality property for foldr.

foldr-universal : ∀ {a b} {A : Set a} (B : ℕ → Set b)
                  (f : ∀ {n} → A → B n → B (suc n)) {e}
                  (h : ∀ {n} → Vec A n → B n) →
                  h [] ≡ e →
                  (∀ {n} x → h ∘ _∷_ x ≗ f {n} x ∘ h) →
                  ∀ {n} → h ≗ foldr B {n} f e
foldr-universal B f     h base step []       = base
foldr-universal B f {e} h base step (x ∷ xs) = begin
  h (x ∷ xs)
    ≡⟨ step x xs ⟩
  f x (h xs)
    ≡⟨ PropEq.cong (f x) (foldr-universal B f h base step xs) ⟩
  f x (foldr B f e xs)
    ∎
  where open ≡-Reasoning

-- A fusion law for foldr.

foldr-fusion : ∀ {a b c} {A : Set a}
                 {B : ℕ → Set b} {f : ∀ {n} → A → B n → B (suc n)} e
                 {C : ℕ → Set c} {g : ∀ {n} → A → C n → C (suc n)}
               (h : ∀ {n} → B n → C n) →
               (∀ {n} x → h ∘ f {n} x ≗ g x ∘ h) →
               ∀ {n} → h ∘ foldr B {n} f e ≗ foldr C g (h e)
foldr-fusion {B = B} {f} e {C} h fuse =
  foldr-universal C _ _ refl (λ x xs → fuse x (foldr B f e xs))

-- The identity function is a fold.

idIsFold : ∀ {a n} {A : Set a} → id ≗ foldr (Vec A) {n} _∷_ []
idIsFold = foldr-universal _ _ id refl (λ _ _ → refl)

-- Proof irrelevance for _[_]=_.

proof-irrelevance-[]= : ∀ {a} {A : Set a} {n} {xs : Vec A n} {i x} →
                        (p q : xs [ i ]= x) → p ≡ q
proof-irrelevance-[]= here            here             = refl
proof-irrelevance-[]= (there xs[i]=x) (there xs[i]=x') =
  PropEq.cong there (proof-irrelevance-[]= xs[i]=x xs[i]=x')

-- _[_]=_ can be expressed using lookup and _≡_.

[]=⇿lookup : ∀ {a n i} {A : Set a} {x} {xs : Vec A n} →
             xs [ i ]= x ⇿ lookup i xs ≡ x
[]=⇿lookup {i = i} {x = x} {xs} = record
  { to         = PropEq.→-to-⟶ to
  ; from       = PropEq.→-to-⟶ (from i xs)
  ; inverse-of = record
    { left-inverse-of  = λ _ → proof-irrelevance-[]= _ _
    ; right-inverse-of = λ _ → PropEq.proof-irrelevance _ _
    }
  }
  where
  to : ∀ {n xs} {i : Fin n} → xs [ i ]= x → lookup i xs ≡ x
  to here            = refl
  to (there xs[i]=x) = to xs[i]=x

  from : ∀ {n} (i : Fin n) xs → lookup i xs ≡ x → xs [ i ]= x
  from zero    (.x ∷ _)  refl = here
  from (suc i) (_  ∷ xs) p    = there (from i xs p)
