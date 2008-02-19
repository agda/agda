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

data [_] (a : Set) : Set where
  []  : [ a ]
  _∷_ : a -> [ a ] -> [ a ]

{-# BUILTIN LIST [_] #-}
{-# BUILTIN NIL  []  #-}
{-# BUILTIN CONS _∷_ #-}

------------------------------------------------------------------------
-- Some operations

_++_ : forall {a} -> [ a ] -> [ a ] -> [ a ]
[]       ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)

map : forall {a b} -> (a -> b) -> [ a ] -> [ b ]
map f []       = []
map f (x ∷ xs) = f x ∷ map f xs

replicate : forall {a} -> (n : ℕ) -> a -> [ a ]
replicate zero    x = []
replicate (suc n) x = x ∷ replicate n x

foldr : {a b : Set} -> (a -> b -> b) -> b -> [ a ] -> b
foldr c n []       = n
foldr c n (x ∷ xs) = c x (foldr c n xs)

foldl : {a b : Set} -> (a -> b -> a) -> a -> [ b ] -> a
foldl c n []       = n
foldl c n (x ∷ xs) = foldl c (c n x) xs

sum : [ ℕ ] -> ℕ
sum = foldr _+_ 0

length : forall {a} -> [ a ] -> ℕ
length = foldr (\_ -> suc) 0

concat : forall {a} -> [ [ a ] ] -> [ a ]
concat = foldr _++_ []

reverse : forall {a} -> [ a ] -> [ a ]
reverse xs = rev xs []
  where
  rev : forall {a} -> [ a ] -> [ a ] -> [ a ]
  rev []       ys = ys
  rev (x ∷ xs) ys = rev xs (x ∷ ys)

filter : forall {a} -> (a -> Bool) -> [ a ] -> [ a ]
filter p []       = []
filter p (x ∷ xs) with p x
... | true  = x ∷ filter p xs
... | false =     filter p xs

null : forall {a} -> [ a ] -> Bool
null []       = true
null (x ∷ xs) = false

-- Possibly the following functions should be called lefts and rights.

inj₁s : forall {a b} -> [ a ⊎ b ] -> [ a ]
inj₁s []            = []
inj₁s (inj₁ x ∷ xs) = x ∷ inj₁s xs
inj₁s (inj₂ x ∷ xs) = inj₁s xs

inj₂s : forall {a b} -> [ a ⊎ b ] -> [ b ]
inj₂s []            = []
inj₂s (inj₁ x ∷ xs) = inj₂s xs
inj₂s (inj₂ x ∷ xs) = x ∷ inj₂s xs

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
downFrom = unfold Singleton f ∘ wrap
  where
  data Singleton : ℕ -> Set where
    wrap : (n : ℕ) -> Singleton n

  f : forall {n} -> Singleton (suc n) -> Maybe (ℕ × Singleton n)
  f {n} (wrap .(suc n)) = just (n , wrap n)

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
  ; mzero = []
  }

ListMonadPlus : RawMonadPlus [_]
ListMonadPlus = record
  { monadZero = ListMonadZero
  ; _++_      = _++_
  }
