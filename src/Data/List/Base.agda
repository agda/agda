------------------------------------------------------------------------
-- The Agda standard library
--
-- Lists, basic types and operations
------------------------------------------------------------------------

module Data.List.Base where

open import Data.Nat.Base using (ℕ; zero; suc; _+_; _*_)
open import Data.Sum as Sum using (_⊎_; inj₁; inj₂)
open import Data.Bool.Base using (Bool; false; true; not; _∧_; _∨_; if_then_else_)
open import Data.Maybe.Base using (Maybe; nothing; just)
open import Data.Product as Prod using (_×_; _,_)
open import Function

infixr 5 _∷_

------------------------------------------------------------------------
-- Types

data List {a} (A : Set a) : Set a where
  []  : List A
  _∷_ : (x : A) (xs : List A) → List A

{-# BUILTIN LIST List #-}
{-# BUILTIN NIL  []   #-}
{-# BUILTIN CONS _∷_  #-}

{-# IMPORT Data.FFI #-}
{-# COMPILED_DATA List Data.FFI.AgdaList [] (:) #-}

------------------------------------------------------------------------
-- Some operations

-- * Basic functions

infixr 5 _++_

[_] : ∀ {a} {A : Set a} → A → List A
[ x ] = x ∷ []

_++_ : ∀ {a} {A : Set a} → List A → List A → List A
[]       ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)

-- Snoc.

infixl 5 _∷ʳ_

_∷ʳ_ : ∀ {a} {A : Set a} → List A → A → List A
xs ∷ʳ x = xs ++ [ x ]

null : ∀ {a} {A : Set a} → List A → Bool
null []       = true
null (x ∷ xs) = false

-- * List transformations

map : ∀ {a b} {A : Set a} {B : Set b} → (A → B) → List A → List B
map f []       = []
map f (x ∷ xs) = f x ∷ map f xs

replicate : ∀ {a} {A : Set a} → (n : ℕ) → A → List A
replicate zero    x = []
replicate (suc n) x = x ∷ replicate n x

zipWith : ∀ {a b c} {A : Set a} {B : Set b} {C : Set c}
          → (A → B → C) → List A → List B → List C
zipWith f (x ∷ xs) (y ∷ ys) = f x y ∷ zipWith f xs ys
zipWith f _        _        = []

zip : ∀ {a b} {A : Set a} {B : Set b} → List A → List B → List (A × B)
zip = zipWith (_,_)

intersperse : ∀ {a} {A : Set a} → A → List A → List A
intersperse x []           = []
intersperse x (y ∷ [])     = [ y ]
intersperse x (y ∷ z ∷ zs) = y ∷ x ∷ intersperse x (z ∷ zs)

-- * Reducing lists (folds)

foldr : ∀ {a b} {A : Set a} {B : Set b} → (A → B → B) → B → List A → B
foldr c n []       = n
foldr c n (x ∷ xs) = c x (foldr c n xs)

foldl : ∀ {a b} {A : Set a} {B : Set b} → (A → B → A) → A → List B → A
foldl c n []       = n
foldl c n (x ∷ xs) = foldl c (c n x) xs

-- ** Special folds

concat : ∀ {a} {A : Set a} → List (List A) → List A
concat = foldr _++_ []

concatMap : ∀ {a b} {A : Set a} {B : Set b} →
            (A → List B) → List A → List B
concatMap f = concat ∘ map f

and : List Bool → Bool
and = foldr _∧_ true

or : List Bool → Bool
or = foldr _∨_ false

any : ∀ {a} {A : Set a} → (A → Bool) → List A → Bool
any p = or ∘ map p

all : ∀ {a} {A : Set a} → (A → Bool) → List A → Bool
all p = and ∘ map p

sum : List ℕ → ℕ
sum = foldr _+_ 0

product : List ℕ → ℕ
product = foldr _*_ 1

length : ∀ {a} {A : Set a} → List A → ℕ
length = foldr (λ _ → suc) 0

reverse : ∀ {a} {A : Set a} → List A → List A
reverse = foldl (λ rev x → x ∷ rev) []

-- * Building lists

-- ** Scans

scanr : ∀ {a b} {A : Set a} {B : Set b} →
        (A → B → B) → B → List A → List B
scanr f e []       = e ∷ []
scanr f e (x ∷ xs) with scanr f e xs
... | []     = []                -- dead branch
... | y ∷ ys = f x y ∷ y ∷ ys

scanl : ∀ {a b} {A : Set a} {B : Set b} →
        (A → B → A) → A → List B → List A
scanl f e []       = e ∷ []
scanl f e (x ∷ xs) = e ∷ scanl f (f e x) xs

-- ** Unfolding

-- Unfold. Uses a measure (a natural number) to ensure termination.

unfold : ∀ {a b} {A : Set a} (B : ℕ → Set b)
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

fromMaybe : ∀ {a} {A : Set a} → Maybe A → List A
fromMaybe (just x) = [ x ]
fromMaybe nothing  = []

-- * Sublists

-- ** Extracting sublists

take : ∀ {a} {A : Set a} → ℕ → List A → List A
take zero    xs       = []
take (suc n) []       = []
take (suc n) (x ∷ xs) = x ∷ take n xs

drop : ∀ {a} {A : Set a} → ℕ → List A → List A
drop zero    xs       = xs
drop (suc n) []       = []
drop (suc n) (x ∷ xs) = drop n xs

splitAt : ∀ {a} {A : Set a} → ℕ → List A → (List A × List A)
splitAt zero    xs       = ([] , xs)
splitAt (suc n) []       = ([] , [])
splitAt (suc n) (x ∷ xs) with splitAt n xs
... | (ys , zs) = (x ∷ ys , zs)

takeWhile : ∀ {a} {A : Set a} → (A → Bool) → List A → List A
takeWhile p []       = []
takeWhile p (x ∷ xs) with p x
... | true  = x ∷ takeWhile p xs
... | false = []

dropWhile : ∀ {a} {A : Set a} → (A → Bool) → List A → List A
dropWhile p []       = []
dropWhile p (x ∷ xs) with p x
... | true  = dropWhile p xs
... | false = x ∷ xs

span : ∀ {a} {A : Set a} → (A → Bool) → List A → (List A × List A)
span p []       = ([] , [])
span p (x ∷ xs) with p x
... | true  = Prod.map (_∷_ x) id (span p xs)
... | false = ([] , x ∷ xs)

break : ∀ {a} {A : Set a} → (A → Bool) → List A → (List A × List A)
break p = span (not ∘ p)

inits : ∀ {a} {A : Set a} → List A → List (List A)
inits []       = [] ∷ []
inits (x ∷ xs) = [] ∷ map (_∷_ x) (inits xs)

tails : ∀ {a} {A : Set a} → List A → List (List A)
tails []       = [] ∷ []
tails (x ∷ xs) = (x ∷ xs) ∷ tails xs

infixl 5 _∷ʳ'_

data InitLast {a} {A : Set a} : List A → Set a where
  []    : InitLast []
  _∷ʳ'_ : (xs : List A) (x : A) → InitLast (xs ∷ʳ x)

initLast : ∀ {a} {A : Set a} (xs : List A) → InitLast xs
initLast []               = []
initLast (x ∷ xs)         with initLast xs
initLast (x ∷ .[])        | []       = [] ∷ʳ' x
initLast (x ∷ .(ys ∷ʳ y)) | ys ∷ʳ' y = (x ∷ ys) ∷ʳ' y

-- * Searching lists

-- ** Searching with a predicate

-- A generalised variant of filter.

gfilter : ∀ {a b} {A : Set a} {B : Set b} →
          (A → Maybe B) → List A → List B
gfilter p []       = []
gfilter p (x ∷ xs) with p x
... | just y  = y ∷ gfilter p xs
... | nothing =     gfilter p xs

filter : ∀ {a} {A : Set a} → (A → Bool) → List A → List A
filter p = gfilter (λ x → if p x then just x else nothing)

partition : ∀ {a} {A : Set a} → (A → Bool) → List A → (List A × List A)
partition p []       = ([] , [])
partition p (x ∷ xs) with p x | partition p xs
... | true  | (ys , zs) = (x ∷ ys , zs)
... | false | (ys , zs) = (ys , x ∷ zs)
