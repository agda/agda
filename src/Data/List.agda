------------------------------------------------------------------------
-- Lists
------------------------------------------------------------------------
{-# OPTIONS --universe-polymorphism #-}

module Data.List where

open import Data.Nat
open import Data.Sum as Sum using (_⊎_; inj₁; inj₂)
open import Data.Bool
open import Data.Maybe using (Maybe; nothing; just)
open import Data.Product as Prod using (_×_; _,_)
open import Data.Function
open import Algebra
import Relation.Binary.PropositionalEquality as PropEq
import Algebra.FunctionProperties as FunProp

infixr 5 _∷_ _++_

------------------------------------------------------------------------
-- Types

data List {ℓ} (A : Set ℓ) : Set ℓ where
  []  : List A
  _∷_ : (x : A) (xs : List A) → List A

{-# BUILTIN LIST List #-}
{-# BUILTIN NIL  []   #-}
{-# BUILTIN CONS _∷_  #-}

------------------------------------------------------------------------
-- Some operations

-- * Basic functions

[_] : ∀ {ℓ} {a : Set ℓ} → a → List a
[ x ] = x ∷ []

_++_ : ∀ {ℓ} {a : Set ℓ} → List a → List a → List a
[]       ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)

-- Snoc.

infixl 5 _∷ʳ_

_∷ʳ_ : ∀ {ℓ} {A : Set ℓ} → List A → A → List A
xs ∷ʳ x = xs ++ [ x ]

null : ∀ {ℓ} {a : Set ℓ} → List a → Bool
null []       = true
null (x ∷ xs) = false

-- * List transformations

map : ∀ {ℓ₁ ℓ₂} {a : Set ℓ₁} {b : Set ℓ₂} → (a → b) → List a → List b
map f []       = []
map f (x ∷ xs) = f x ∷ map f xs

reverse : ∀ {ℓ} {a : Set ℓ} → List a → List a
reverse xs = rev xs []
  where
  rev : ∀ {ℓ} {a : Set ℓ} → List a → List a → List a
  rev []       ys = ys
  rev (x ∷ xs) ys = rev xs (x ∷ ys)

replicate : ∀ {ℓ} {a : Set ℓ} → (n : ℕ) → a → List a
replicate zero    x = []
replicate (suc n) x = x ∷ replicate n x

zipWith : ∀ {ℓ₁ ℓ₂ ℓ₃} {A : Set ℓ₁} {B : Set ℓ₂} {C : Set ℓ₃}
          → (A → B → C) → List A → List B → List C
zipWith f (x ∷ xs) (y ∷ ys) = f x y ∷ zipWith f xs ys
zipWith f _        _        = []

zip : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} {B : Set ℓ₂} → List A → List B → List (A × B)
zip = zipWith (_,_)

intersperse : ∀ {ℓ} {A : Set ℓ} → A → List A → List A
intersperse x []           = []
intersperse x (y ∷ [])     = [ y ]
intersperse x (y ∷ z ∷ zs) = y ∷ x ∷ intersperse x (z ∷ zs)

-- * Reducing lists (folds)

foldr : ∀ {ℓ₁ ℓ₂} {a : Set ℓ₁} {b : Set ℓ₂} → (a → b → b) → b → List a → b
foldr c n []       = n
foldr c n (x ∷ xs) = c x (foldr c n xs)

foldl : ∀ {ℓ₁ ℓ₂} {a : Set ℓ₁} {b : Set ℓ₂} → (a → b → a) → a → List b → a
foldl c n []       = n
foldl c n (x ∷ xs) = foldl c (c n x) xs

-- ** Special folds

concat : ∀ {ℓ} {a : Set ℓ} → List (List a) → List a
concat = foldr _++_ []

concatMap : ∀ {ℓ₁ ℓ₂} {a : Set ℓ₁} {b : Set ℓ₂} → (a → List b) → List a → List b
concatMap f = concat ∘ map f

and : List Bool → Bool
and = foldr _∧_ true

or : List Bool → Bool
or = foldr _∨_ false

any : ∀ {ℓ} {a : Set ℓ} → (a → Bool) → List a → Bool
any p = or ∘ map p

all : ∀ {ℓ} {a : Set ℓ} → (a → Bool) → List a → Bool
all p = and ∘ map p

sum : List ℕ → ℕ
sum = foldr _+_ 0

product : List ℕ → ℕ
product = foldr _*_ 1

length : ∀ {ℓ} {a : Set ℓ} → List a → ℕ
length = foldr (λ _ → suc) 0

-- * Building lists

-- ** Scans

scanr : ∀ {ℓ₁ ℓ₂} {a : Set ℓ₁} {b : Set ℓ₂} → (a → b → b) → b → List a → List b
scanr f e []       = e ∷ []
scanr f e (x ∷ xs) with scanr f e xs
... | []     = []                -- dead branch
... | y ∷ ys = f x y ∷ y ∷ ys

scanl : ∀ {ℓ₁ ℓ₂} {a : Set ℓ₁} {b : Set ℓ₂} → (a → b → a) → a → List b → List a
scanl f e []       = e ∷ []
scanl f e (x ∷ xs) = e ∷ scanl f (f e x) xs

-- ** Unfolding

-- Unfold. Uses a measure (a natural number) to ensure termination.

unfold : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} (B : ℕ → Set ℓ₂)
         (f : ∀ {n} → B (suc n) → Maybe (A × B n)) →
         ∀ {n} → B n → List A
unfold B f {n = zero}  s = []
unfold B f {n = suc n} s with f s
... | nothing       = []
... | just (x , s') = x ∷ unfold B f s'

-- downFrom 3 = 2 ∷ 1 ∷ 0 ∷ [].

downFrom : ℕ → List ℕ
downFrom n = unfold Singleton f (wrap n)
  where
  data Singleton : ℕ → Set where
    wrap : (n : ℕ) → Singleton n

  f : ∀ {n} → Singleton (suc n) → Maybe (ℕ × Singleton n)
  f {n} (wrap .(suc n)) = just (n , wrap n)

-- ** Conversions

fromMaybe : ∀ {ℓ} {A : Set ℓ} → Maybe A → List A
fromMaybe (just x) = [ x ]
fromMaybe nothing  = []

-- * Sublists

-- ** Extracting sublists

take : ∀ {ℓ} {a : Set ℓ} → ℕ → List a → List a
take zero    xs       = []
take (suc n) []       = []
take (suc n) (x ∷ xs) = x ∷ take n xs

drop : ∀ {ℓ} {a : Set ℓ} → ℕ → List a → List a
drop zero    xs       = xs
drop (suc n) []       = []
drop (suc n) (x ∷ xs) = drop n xs

splitAt : ∀ {ℓ} {a : Set ℓ} → ℕ → List a → (List a × List a)
splitAt zero    xs       = ([] , xs)
splitAt (suc n) []       = ([] , [])
splitAt (suc n) (x ∷ xs) with splitAt n xs
... | (ys , zs) = (x ∷ ys , zs)

takeWhile : ∀ {ℓ} {a : Set ℓ} → (a → Bool) → List a → List a
takeWhile p []       = []
takeWhile p (x ∷ xs) with p x
... | true  = x ∷ takeWhile p xs
... | false = []

dropWhile : ∀ {ℓ} {a : Set ℓ} → (a → Bool) → List a → List a
dropWhile p []       = []
dropWhile p (x ∷ xs) with p x
... | true  = dropWhile p xs
... | false = x ∷ xs

span : ∀ {ℓ} {a : Set ℓ} → (a → Bool) → List a → (List a × List a)
span p []       = ([] , [])
span p (x ∷ xs) with p x
... | true  = Prod.map (_∷_ x) id (span p xs)
... | false = ([] , x ∷ xs)

break : ∀ {ℓ} {a : Set ℓ} → (a → Bool) → List a → (List a × List a)
break p = span (not ∘ p)

inits : ∀ {ℓ} {a : Set ℓ} →  List a → List (List a)
inits []       = [] ∷ []
inits (x ∷ xs) = [] ∷ map (_∷_ x) (inits xs)

tails : ∀ {ℓ} {a : Set ℓ} → List a → List (List a)
tails []       = [] ∷ []
tails (x ∷ xs) = (x ∷ xs) ∷ tails xs

infixl 5 _∷ʳ'_

data InitLast {ℓ} {A : Set ℓ} : List A → Set ℓ where
  []    : InitLast []
  _∷ʳ'_ : (xs : List A) (x : A) → InitLast (xs ∷ʳ x)

initLast : ∀ {ℓ} {A : Set ℓ} (xs : List A) → InitLast xs
initLast []               = []
initLast (x ∷ xs)         with initLast xs
initLast (x ∷ .[])        | []       = [] ∷ʳ' x
initLast (x ∷ .(ys ∷ʳ y)) | ys ∷ʳ' y = (x ∷ ys) ∷ʳ' y

-- * Searching lists

-- ** Searching with a predicate

-- A generalised variant of filter.

gfilter : ∀ {ℓ₁ ℓ₂} {a : Set ℓ₁} {b : Set ℓ₂} → (a → Maybe b) → List a → List b
gfilter p []       = []
gfilter p (x ∷ xs) with p x
... | just y  = y ∷ gfilter p xs
... | nothing =     gfilter p xs

filter : ∀ {ℓ} {a : Set ℓ} → (a → Bool) → List a → List a
filter p = gfilter (λ x → if p x then just x else nothing)

partition : ∀ {ℓ} {a : Set ℓ} → (a → Bool) → List a → (List a × List a)
partition p []       = ([] , [])
partition p (x ∷ xs) with p x | partition p xs
... | true  | (ys , zs) = (x ∷ ys , zs)
... | false | (ys , zs) = (ys , x ∷ zs)

------------------------------------------------------------------------
-- List monoid

monoid : Set → Monoid
monoid A = record
  { carrier  = List A
  ; _≈_      = _≡_
  ; _∙_      = _++_
  ; ε        = []
  ; isMonoid = record
    { isSemigroup = record
      { isEquivalence = PropEq.isEquivalence
      ; assoc         = assoc
      ; ∙-pres-≈      = cong₂ _++_
      }
    ; identity = ((λ _ → refl) , identity)
    }
  }
  where
  open PropEq
  open FunProp _≡_

  identity : RightIdentity [] _++_
  identity []       = refl
  identity (x ∷ xs) = cong (_∷_ x) (identity xs)

  assoc : Associative _++_
  assoc []       ys zs = refl
  assoc (x ∷ xs) ys zs = cong (_∷_ x) (assoc xs ys zs)

------------------------------------------------------------------------
-- List monad

open import Category.Monad

monad : RawMonad List
monad = record
  { return = λ x → x ∷ []
  ; _>>=_  = λ xs f → concat (map f xs)
  }

monadZero : RawMonadZero List
monadZero = record
  { monad = monad
  ; ∅     = []
  }

monadPlus : RawMonadPlus List
monadPlus = record
  { monadZero = monadZero
  ; _∣_       = _++_
  }

------------------------------------------------------------------------
-- Monadic functions

private
 module Monadic {M} (Mon : RawMonad M) where

  open RawMonad Mon

  sequence : ∀ {A : Set} → List (M A) → M (List A)
  sequence []       = return []
  sequence (x ∷ xs) = _∷_ <$> x ⊛ sequence xs

  mapM : ∀ {ℓ} {A : Set ℓ} {B} → (A → M B) → List A → M (List B)
  mapM f = sequence ∘ map f

open Monadic public
