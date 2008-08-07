------------------------------------------------------------------------
-- Lists
------------------------------------------------------------------------

module Data.List where

open import Data.Nat
open import Data.Sum
open import Data.Bool
open import Data.Maybe
open import Data.Product
open import Data.Function

infixr 5 _∷_ _++_

------------------------------------------------------------------------
-- The type

data [_] (A : Set) : Set where
  []  : [ A ]
  _∷_ : (x : A) (xs : [ A ]) -> [ A ]

{-# BUILTIN LIST [_] #-}
{-# BUILTIN NIL  []  #-}
{-# BUILTIN CONS _∷_ #-}

------------------------------------------------------------------------
-- Some operations

-- * Basic functions

singleton : forall {a} -> a -> [ a ]
singleton x = x ∷ []

_++_ : forall {a} -> [ a ] -> [ a ] -> [ a ]
[]       ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)

null : forall {a} -> [ a ] -> Bool
null []       = true
null (x ∷ xs) = false

-- * List transformations

map : forall {a b} -> (a -> b) -> [ a ] -> [ b ]
map f []       = []
map f (x ∷ xs) = f x ∷ map f xs

reverse : forall {a} -> [ a ] -> [ a ]
reverse xs = rev xs []
  where
  rev : forall {a} -> [ a ] -> [ a ] -> [ a ]
  rev []       ys = ys
  rev (x ∷ xs) ys = rev xs (x ∷ ys)

replicate : forall {a} -> (n : ℕ) -> a -> [ a ]
replicate zero    x = []
replicate (suc n) x = x ∷ replicate n x

-- * Reducing lists (folds)

foldr : {a b : Set} -> (a -> b -> b) -> b -> [ a ] -> b
foldr c n []       = n
foldr c n (x ∷ xs) = c x (foldr c n xs)

foldl : {a b : Set} -> (a -> b -> a) -> a -> [ b ] -> a
foldl c n []       = n
foldl c n (x ∷ xs) = foldl c (c n x) xs

-- ** Special folds

concat : forall {a} -> [ [ a ] ] -> [ a ]
concat = foldr _++_ []

concatMap : forall {a b} -> (a -> [ b ]) ->  [ a ] -> [ b ]
concatMap f = concat ∘ map f

and : [ Bool ] -> Bool
and = foldr _∧_ true

or : [ Bool ] -> Bool
or = foldr _∨_ false

any : forall {a} -> (a -> Bool) -> [ a ] -> Bool
any p = or ∘ map p

all : forall {a} -> (a -> Bool) -> [ a ] -> Bool
all p = and ∘ map p

sum : [ ℕ ] -> ℕ
sum = foldr _+_ 0

product : [ ℕ ] -> ℕ
product = foldr _*_ 1

length : forall {a} -> [ a ] -> ℕ
length = foldr (\_ -> suc) 0

-- * Building lists

-- ** Scans

scanr : forall {a b} -> (a -> b -> b) -> b -> [ a ] -> [ b ]
scanr f e []       = e ∷ []
scanr f e (x ∷ xs) with scanr f e xs
... | []     = []                -- dead branch
... | y ∷ ys = f x y ∷ y ∷ ys

scanl : forall {a b} -> (a -> b -> a) -> a -> [ b ] -> [ a ]
scanl f e []       = e ∷ []
scanl f e (x ∷ xs) = e ∷ scanl f (f e x) xs

-- ** Unfolding

-- Unfold. Uses a measure (a natural number) to ensure termination.

unfold :  {A : Set} (B : ℕ -> Set)
          (f : forall {n} -> B (suc n) -> Maybe (A × B n))
       -> forall {n} -> B n -> [ A ]
unfold B f {n = zero}  s = []
unfold B f {n = suc n} s with f s
... | nothing       = []
... | just (x , s') = x ∷ unfold B f s'

-- downFrom 3 = 2 ∷ 1 ∷ 0 ∷ [].

downFrom : ℕ -> [ ℕ ]
downFrom n = unfold Singleton f (wrap n)
  where
  data Singleton : ℕ -> Set where
    wrap : (n : ℕ) -> Singleton n

  f : forall {n} -> Singleton (suc n) -> Maybe (ℕ × Singleton n)
  f {n} (wrap .(suc n)) = just (n , wrap n)

-- * Sublists

-- ** Extracting sublists

take : forall {a} -> ℕ -> [ a ] -> [ a ]
take zero    xs       = []
take (suc n) []       = []
take (suc n) (x ∷ xs) = x ∷ take n xs

drop : forall {a} -> ℕ -> [ a ] -> [ a ]
drop zero    xs       = xs
drop (suc n) []       = []
drop (suc n) (x ∷ xs) = drop n xs

splitAt : forall {a} -> ℕ -> [ a ] -> ([ a ] × [ a ])
splitAt zero    xs       = ([] , xs)
splitAt (suc n) []       = ([] , [])
splitAt (suc n) (x ∷ xs) with splitAt n xs
... | (ys , zs) = (x ∷ ys , zs)

takeWhile : forall {a} -> (a -> Bool) -> [ a ] -> [ a ]
takeWhile p []       = []
takeWhile p (x ∷ xs) with p x
... | true  = x ∷ takeWhile p xs
... | false = []

dropWhile : forall {a} -> (a -> Bool) -> [ a ] -> [ a ]
dropWhile p []       = []
dropWhile p (x ∷ xs) with p x
... | true  = dropWhile p xs
... | false = x ∷ xs

span : forall {a} -> (a -> Bool) -> [ a ] -> ([ a ] × [ a ])
span p []       = ([] , [])
span p (x ∷ xs) with p x
... | true  = map-× (_∷_ x) id (span p xs)
... | false = ([] , x ∷ xs)

break : forall {a} -> (a -> Bool) -> [ a ] -> ([ a ] × [ a ])
break p = span (not ∘ p)

inits : forall {a} ->  [ a ] -> [ [ a ] ]
inits []       = [] ∷ []
inits (x ∷ xs) = [] ∷ map (_∷_ x) (inits xs)

tails : forall {a} -> [ a ] -> [ [ a ] ]
tails []       = [] ∷ []
tails (x ∷ xs) = (x ∷ xs) ∷ tails xs

-- * Searching lists

-- ** Searching with a predicate

filter : forall {a} -> (a -> Bool) -> [ a ] -> [ a ]
filter p []       = []
filter p (x ∷ xs) with p x
... | true  = x ∷ filter p xs
... | false =     filter p xs

partition : forall {a} -> (a -> Bool) -> [ a ] -> ([ a ] × [ a ])
partition p []       = ([] , [])
partition p (x ∷ xs) with p x | partition p xs
... | true  | (ys , zs) = (x ∷ ys , zs)
... | false | (ys , zs) = (ys , x ∷ zs)

-- Possibly the following functions should be called lefts and rights.

inj₁s : forall {a b} -> [ a ⊎ b ] -> [ a ]
inj₁s []            = []
inj₁s (inj₁ x ∷ xs) = x ∷ inj₁s xs
inj₁s (inj₂ x ∷ xs) = inj₁s xs

inj₂s : forall {a b} -> [ a ⊎ b ] -> [ b ]
inj₂s []            = []
inj₂s (inj₁ x ∷ xs) = inj₂s xs
inj₂s (inj₂ x ∷ xs) = x ∷ inj₂s xs

catMaybes : forall {A} -> [ Maybe A ] -> [ A ]
catMaybes = concat ∘ map (maybe singleton [])

------------------------------------------------------------------------
-- List monad

open import Category.Monad

ListMonad : RawMonad [_]
ListMonad = record
  { return = \x -> x ∷ []
  ; _>>=_  = \xs f -> concat (map f xs)
  }

ListMonadZero : RawMonadZero [_]
ListMonadZero = record
  { monad = ListMonad
  ; ∅     = []
  }

ListMonadPlus : RawMonadPlus [_]
ListMonadPlus = record
  { monadZero = ListMonadZero
  ; _∣_       = _++_
  }
