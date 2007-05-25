------------------------------------------------------------------------
-- Small prelude
------------------------------------------------------------------------

module Prelude where

infixl 6 _+_
infixr 5 _∷_ _++_
infixr 3 _∨_
infix  2 ¬_

------------------------------------------------------------------------
-- Some "logic"

data ⊥ : Set where

¬_ : Set -> Set
¬ a = a -> ⊥

------------------------------------------------------------------------
-- Maybe and Dec

data Maybe (a : Set) : Set where
  just    : a -> Maybe a
  nothing :      Maybe a

data Dec (a : Set) : Set where
  yes :   a -> Dec a
  no  : ¬ a -> Dec a

------------------------------------------------------------------------
-- Lists

data [_] (a : Set) : Set where
  []  : [ a ]
  _∷_ : a -> [ a ] -> [ a ]

_++_ : forall {a} -> [ a ] -> [ a ] -> [ a ]
[]       ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)

------------------------------------------------------------------------
-- Natural numbers

data ℕ : Set where
  zero : ℕ
  suc  : ℕ -> ℕ

_+_ : ℕ -> ℕ -> ℕ
zero  + n = n
suc m + n = suc (m + n)

{-# BUILTIN NATURAL ℕ    #-}
{-# BUILTIN ZERO    zero #-}
{-# BUILTIN SUC     suc  #-}
{-# BUILTIN NATPLUS _+_  #-}

------------------------------------------------------------------------
-- Booleans

data Bool : Set where
  true  : Bool
  false : Bool

_∨_ : Bool -> Bool -> Bool
true  ∨ _ = true
false ∨ b = b
