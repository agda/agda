------------------------------------------------------------------------
-- The Agda standard library
--
-- Lists, basic types and operations
------------------------------------------------------------------------

module Data.List.Base where

open import Data.Nat.Base using (ℕ; zero; suc; _+_; _*_)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.Sum as Sum using (_⊎_; inj₁; inj₂)
open import Data.Bool.Base
  using (Bool; false; true; not; _∧_; _∨_; if_then_else_)
open import Data.Maybe.Base using (Maybe; nothing; just)
open import Data.Product as Prod using (_×_; _,_)
open import Function using (id; _∘_)
open import Relation.Nullary using (yes; no)
open import Relation.Unary using (Decidable)

------------------------------------------------------------------------
-- Types

open import Agda.Builtin.List public
  using (List; []; _∷_)

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

-- applyUpTo 3 = f0 ∷ f1 ∷ f2 ∷ [].

applyUpTo : ∀ {a} {A : Set a} → (ℕ → A) → ℕ → List A
applyUpTo f zero    = []
applyUpTo f (suc n) = f zero ∷ applyUpTo (f ∘ suc) n

-- upTo 3 = 0 ∷ 1 ∷ 2 ∷ [].

upTo : ℕ → List ℕ
upTo = applyUpTo id

-- applyDownFrom 3 = f2 ∷ f1 ∷ f0 ∷ [].

applyDownFrom : ∀ {a} {A : Set a} → (ℕ → A) → ℕ → List A
applyDownFrom f zero = []
applyDownFrom f (suc n) = f n ∷ applyDownFrom f n

-- downFrom 3 = 2 ∷ 1 ∷ 0 ∷ [].

downFrom : ℕ → List ℕ
downFrom = applyDownFrom id

-- tabulate f = f 0 ∷ f 1 ∷ ... ∷ f n ∷ []

tabulate : ∀ {a n} {A : Set a} (f : Fin n → A) → List A
tabulate {_} {zero}  f = []
tabulate {_} {suc n} f = f fzero ∷ tabulate (f ∘ fsuc)

allFin : ∀ n → List (Fin n)
allFin n = tabulate id

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

mapMaybe : ∀ {a b} {A : Set a} {B : Set b} →
          (A → Maybe B) → List A → List B
mapMaybe p []       = []
mapMaybe p (x ∷ xs) with p x
... | just y  = y ∷ mapMaybe p xs
... | nothing =     mapMaybe p xs

-- * Searching lists

filter : ∀ {a p} {A : Set a} {P : A → Set p} →
         Decidable P → List A → List A
filter P? [] = []
filter P? (x ∷ xs) with P? x
... | no  _ = filter P? xs
... | yes _ = x ∷ filter P? xs

partition : ∀ {a p} {A : Set a} {P : A → Set p} →
            Decidable P → List A → (List A × List A)
partition P? []       = ([] , [])
partition P? (x ∷ xs) with P? x | partition P? xs
... | yes _ | (ys , zs) = (x ∷ ys , zs)
... | no  _ | (ys , zs) = (ys , x ∷ zs)

------------------------------------------------------------------------
-- DEPRECATED
------------------------------------------------------------------------

gfilter = mapMaybe

-- Please use `filter` instead
boolFilter : ∀ {a} {A : Set a} → (A → Bool) → List A → List A
boolFilter p = mapMaybe (λ x → if p x then just x else nothing)

-- Please use `partition` instead
boolPartition : ∀ {a} {A : Set a} → (A → Bool) → List A → (List A × List A)
boolPartition p []       = ([] , [])
boolPartition p (x ∷ xs) with p x | boolPartition p xs
... | true  | (ys , zs) = (x ∷ ys , zs)
... | false | (ys , zs) = (ys , x ∷ zs)

