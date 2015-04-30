module Common.List where

open import Common.Nat

data List A : Set where
  [] : List A
  _∷_ : A → List A → List A

infixr 40 _∷_ _++_

_++_ : ∀ {A : Set} → List A → List A → List A
[]       ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)

{-# BUILTIN LIST List #-}
{-# BUILTIN NIL []    #-}
{-# BUILTIN CONS _∷_  #-}

{-# COMPILED_DATA List [] [] (:) #-}
{-# COMPILED_DATA_UHC List __LIST__ __NIL__ __CONS__ #-}

map : ∀ {A B} -> (A -> B) -> List A -> List B
map _ []        = []
map f (x ∷ xs) = f x ∷ map f xs

length : {A : Set} -> List A -> Nat
length [] = 0
length (x ∷ xs) = 1 + length xs
