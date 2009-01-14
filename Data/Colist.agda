------------------------------------------------------------------------
-- Coinductive lists
------------------------------------------------------------------------

module Data.Colist where

open import Coinduction
open import Data.Bool  using (Bool; true; false)
open import Data.Maybe using (Maybe; nothing; just)
open import Data.Nat   using (ℕ; zero; suc)
open import Data.List  using (List; []; _∷_)
open import Relation.Binary

------------------------------------------------------------------------
-- The type

infixr 5 _∷_

data Colist (A : Set) : Set where
  []  : Colist A
  _∷_ : (x : A) (xs : ∞ (Colist A)) → Colist A

------------------------------------------------------------------------
-- Some operations

null : ∀ {A} → Colist A → Bool
null []      = true
null (_ ∷ _) = false

map : ∀ {A B} → (A → B) → Colist A → Colist B
map f []       = []
map f (x ∷ xs) = f x ∷ rec
  where rec ~ ♯ map f (♭ xs)

fromList : ∀ {A} → List A → Colist A
fromList []       = []
fromList (x ∷ xs) = x ∷ ♯ fromList xs

take : ∀ {A} → ℕ → Colist A → List A
take zero    xs       = []
take (suc n) []       = []
take (suc n) (x ∷ xs) = take n (♭ xs)

lookup : ∀ {A} → ℕ → Colist A → Maybe A
lookup n       []       = nothing
lookup zero    (x ∷ xs) = just x
lookup (suc n) (x ∷ xs) = lookup n (♭ xs)

infixr 5 _++_

_++_ : ∀ {A} → Colist A → Colist A → Colist A
[]       ++ ys = []
(x ∷ xs) ++ ys = x ∷ rec
  where rec ~ ♯ (♭ xs ++ ys)

[_] : ∀ {A} → A → Colist A
[ x ] = x ∷ ♯ []

------------------------------------------------------------------------
-- Equality and other relations

infix 4 _≈_

data _≈_ {A} : (xs ys : Colist A) → Set where
  []  :                                       []     ≈ []
  _∷_ : ∀ x {xs ys} (xs≈ : ∞ (♭ xs ≈ ♭ ys)) → x ∷ xs ≈ x ∷ ys

infix 4 _∈_

data _∈_ {A : Set} : A → Colist A → Set where
  here  : ∀ {x   xs}                   → x ∈ x ∷ xs
  there : ∀ {x y xs} (x∈xs : x ∈ ♭ xs) → x ∈ y ∷ xs

infix 4 _PrefixOf_

data _PrefixOf_ {A : Set} : Colist A → Colist A → Set where
  []  : ∀ {ys}                       → []     PrefixOf ys
  _∷_ : ∀ x {xs ys}
        (p : ∞ (♭ xs PrefixOf ♭ ys)) → x ∷ xs PrefixOf x ∷ ys

------------------------------------------------------------------------
-- Some proofs

setoid : Set → Setoid
setoid A = record
  { carrier       = Colist A
  ; _≈_           = _≈_ {A}
  ; isEquivalence = record
    { refl  = refl
    ; sym   = sym
    ; trans = trans
    }
  }
  where
  refl : Reflexive _≈_
  refl {[]}     = []
  refl {x ∷ xs} = x ∷ rec
    where rec ~ ♯ refl

  sym : Symmetric _≈_
  sym []        = []
  sym (x ∷ xs≈) = x ∷ rec
    where rec ~ ♯ sym (♭ xs≈)

  trans : Transitive _≈_
  trans []        []         = []
  trans (x ∷ xs≈) (.x ∷ ys≈) = x ∷ rec
    where rec ~ ♯ trans (♭ xs≈) (♭ ys≈)

map-cong : ∀ {A B} (f : A → B) {xs ys : Colist A} →
           xs ≈ ys → map f xs ≈ map f ys
map-cong f []        = []
map-cong f (x ∷ xs≈) = f x ∷ rec
  where rec ~ ♯ map-cong f (♭ xs≈)
