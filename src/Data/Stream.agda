------------------------------------------------------------------------
-- Streams
------------------------------------------------------------------------

module Data.Stream where

open import Coinduction
open import Data.Colist using (Colist; []; _∷_)
open import Data.Vec    using (Vec;    []; _∷_)
open import Data.Nat using (ℕ; zero; suc)
open import Relation.Binary

------------------------------------------------------------------------
-- The type

infixr 5 _∷_

data Stream (A : Set) : Set where
  _∷_ : (x : A) (xs : ∞ (Stream A)) → Stream A

------------------------------------------------------------------------
-- Some operations

head : forall {A} -> Stream A -> A
head (x ∷ xs) = x

tail : forall {A} -> Stream A -> Stream A
tail (x ∷ xs) = ♭ xs

map : ∀ {A B} → (A → B) → Stream A → Stream B
map f (x ∷ xs) = f x ∷ ♯ map f (♭ xs)

zipWith : forall {A B C} ->
          (A -> B -> C) -> Stream A -> Stream B -> Stream C
zipWith _∙_ (x ∷ xs) (y ∷ ys) = (x ∙ y) ∷ ♯ zipWith _∙_ (♭ xs) (♭ ys)

take : ∀ {A} (n : ℕ) → Stream A → Vec A n
take zero    xs       = []
take (suc n) (x ∷ xs) = x ∷ take n (♭ xs)

drop : ∀ {A} -> ℕ -> Stream A -> Stream A
drop zero    xs       = xs
drop (suc n) (x ∷ xs) = drop n (♭ xs)

repeat : forall {A} -> A -> Stream A
repeat x = x ∷ ♯ repeat x

iterate : ∀ {A} → (A → A) → A → Stream A
iterate f x = x ∷ ♯ iterate f (f x)

-- Interleaves the two streams.

infixr 5 _⋎_

_⋎_ : ∀ {A} → Stream A → Stream A → Stream A
(x ∷ xs) ⋎ ys = x ∷ ♯ (ys ⋎ ♭ xs)

toColist : ∀ {A} → Stream A → Colist A
toColist (x ∷ xs) = x ∷ ♯ toColist (♭ xs)

lookup : ∀ {A} → ℕ → Stream A → A
lookup zero    (x ∷ xs) = x
lookup (suc n) (x ∷ xs) = lookup n (♭ xs)

infixr 5 _++_

_++_ : ∀ {A} → Colist A → Stream A → Stream A
[]       ++ ys = ys
(x ∷ xs) ++ ys = x ∷ ♯ (♭ xs ++ ys)

------------------------------------------------------------------------
-- Equality and other relations

-- xs ≈ ys means that xs and ys are equal.

infix 4 _≈_

data _≈_ {A} : (xs ys : Stream A) → Set where
  _∷_ : ∀ x {xs ys} (xs≈ : ∞ (♭ xs ≈ ♭ ys)) → x ∷ xs ≈ x ∷ ys

-- x ∈ xs means that x is a member of xs.

infix 4 _∈_

data _∈_ {A : Set} : A → Stream A → Set where
  here  : ∀ {x   xs}                   → x ∈ x ∷ xs
  there : ∀ {x y xs} (x∈xs : x ∈ ♭ xs) → x ∈ y ∷ xs

-- xs ⊑ ys means that xs is a prefix of ys.

infix 4 _⊑_

data _⊑_ {A : Set} : Colist A → Stream A → Set where
  []  : ∀ {ys}                            → []     ⊑ ys
  _∷_ : ∀ x {xs ys} (p : ∞ (♭ xs ⊑ ♭ ys)) → x ∷ xs ⊑ x ∷ ys

------------------------------------------------------------------------
-- Some proofs

setoid : Set → Setoid
setoid A = record
  { carrier       = Stream A
  ; _≈_           = _≈_ {A}
  ; isEquivalence = record
    { refl  = refl
    ; sym   = sym
    ; trans = trans
    }
  }
  where
  refl : Reflexive _≈_
  refl {x ∷ xs} = x ∷ ♯ refl

  sym : Symmetric _≈_
  sym (x ∷ xs≈) = x ∷ ♯ sym (♭ xs≈)

  trans : Transitive _≈_
  trans (x ∷ xs≈) (.x ∷ ys≈) = x ∷ ♯ trans (♭ xs≈) (♭ ys≈)

map-cong : ∀ {A B} (f : A → B) {xs ys : Stream A} →
           xs ≈ ys → map f xs ≈ map f ys
map-cong f (x ∷ xs≈) = f x ∷ ♯ map-cong f (♭ xs≈)
