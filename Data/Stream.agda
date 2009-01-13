------------------------------------------------------------------------
-- Streams
------------------------------------------------------------------------

module Data.Stream where

open import Coinduction
open import Data.List   using (List;   []; _∷_)
open import Data.Colist using (Colist; []; _∷_)
open import Data.Nat using (ℕ; zero; suc)
open import Relation.Binary
open import Relation.Binary.PropositionalEquality

------------------------------------------------------------------------
-- The type

infixr 5 _∷_

data Stream (A : Set) : Set where
  _∷_ : (x : A) (xs : ∞ (Stream A)) → Stream A

------------------------------------------------------------------------
-- Some operations

map : ∀ {A B} → (A → B) → Stream A → Stream B
map f (x ∷ xs) = f x ∷ rec
  where rec ~ ♯ map f (♭ xs)

take : ∀ {A} → ℕ → Stream A → List A
take zero    xs       = []
take (suc n) (x ∷ xs) = take n (♭ xs)

toColist : ∀ {A} → Stream A → Colist A
toColist (x ∷ xs) = x ∷ rec
  where rec ~ ♯ toColist (♭ xs)

lookup : ∀ {A} → ℕ → Stream A → A
lookup zero    (x ∷ xs) = x
lookup (suc n) (x ∷ xs) = lookup n (♭ xs)

infixr 5 _++′_ _++_

_++′_ : ∀ {A} → Colist A → Stream A → Stream A
[]       ++′ ys = ys
(x ∷ xs) ++′ ys = x ∷ rec
  where rec ~ ♯ (♭ xs ++′ ys)

_++_ : ∀ {A} → Stream A → Stream A → Stream A
xs ++ ys = toColist xs ++′ ys

------------------------------------------------------------------------
-- Equality and other relations

infix 4 _≈_

data _≈_ {A} : (xs ys : Stream A) → Set where
  _∷_ : ∀ x {xs ys} (xs≈ : ∞ (♭ xs ≈ ♭ ys)) → x ∷ xs ≈ x ∷ ys

infix 4 _∈_

data _∈_ {A : Set} : A → Stream A → Set where
  here  : ∀ {x   xs}                   → x ∈ x ∷ xs
  there : ∀ {x y xs} (x∈xs : x ∈ ♭ xs) → x ∈ y ∷ xs

infix 4 _PrefixOf_

data _PrefixOf_ {A : Set} : Colist A → Stream A → Set where
  []  : ∀ {ys}                       → []     PrefixOf ys
  _∷_ : ∀ x {xs ys}
        (p : ∞ (♭ xs PrefixOf ♭ ys)) → x ∷ xs PrefixOf x ∷ ys

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
  refl {x ∷ xs} = x ∷ rec
    where rec ~ ♯ refl

  sym : Symmetric _≈_
  sym (x ∷ xs≈) = x ∷ rec
    where rec ~ ♯ sym (♭ xs≈)

  trans : Transitive _≈_
  trans (x ∷ xs≈) (.x ∷ ys≈) = x ∷ rec
    where rec ~ ♯ trans (♭ xs≈) (♭ ys≈)

map-cong : ∀ {A B} (f : A → B) {xs ys : Stream A} →
           xs ≈ ys → map f xs ≈ map f ys
map-cong f (x ∷ xs≈) = f x ∷ rec
  where rec ~ ♯ map-cong f (♭ xs≈)
