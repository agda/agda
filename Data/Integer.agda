------------------------------------------------------------------------
-- Integers
------------------------------------------------------------------------

module Data.Integer where

import Data.Nat as N
open N using (ℕ)
open import Data.String

infix  8 +_ -_
infixl 7 _*_ _⊓_
infixl 6 _+_ _-_ _⊔_

infix  8 :+_ :-_
infixl 7 _*'_
infixl 6 _+'_ _-'_

------------------------------------------------------------------------
-- The types

abstract

  data ℤ : Set where
    :-_ : ℕ -> ℤ
    :0  : ℤ
    :+_ : ℕ -> ℤ

------------------------------------------------------------------------
-- Arithmetic

abstract

  0# : ℤ
  0# = :0

  suc : ℤ -> ℤ
  suc (:- N.suc n) = :- n
  suc (:- N.zero)  = :0
  suc :0           = :+ 0
  suc (:+ n)       = :+ N.suc n

  private module G = N.GeneralisedArithmetic 0# suc

  pred : ℤ -> ℤ
  pred (:- n)       = :- N.suc n
  pred :0           = :- 0
  pred (:+ N.zero)  = :0
  pred (:+ N.suc n) = :+ n

  +_ : ℕ -> ℤ
  + N.zero  = :0
  + N.suc n = :+ n

  -_ : ℤ -> ℤ
  - :- n = :+ n
  - :0   = :0
  - :+ n = :- n

  private
    _+'_ : ℕ -> ℤ -> ℤ
    _+'_ = G.add

    _-'_ : ℕ -> ℤ -> ℤ
    n       -' :0         = + n
    N.zero  -' i          = - i
    N.suc n -' :+ N.zero  = + n
    N.suc n -' :+ N.suc m = n -' :+ m
    n       -' :- i       = n +' :+ i

  _+_ : ℤ -> ℤ -> ℤ
  :- n + i = - (N.suc n -' i)
  :0   + i = i
  :+ n + i = N.suc n +' i

  _-_ : ℤ -> ℤ -> ℤ
  :- n - i = - (N.suc n +' i)
  :0   - i = - i
  :+ n - i = N.suc n -' i

  private
    _*'_ : ℕ -> ℤ -> ℤ
    _*'_ = G.mul _+_

  _*_ : ℤ -> ℤ -> ℤ
  :- n * i = - (N.suc n *' i)
  :0   * i = :0
  :+ n * i = N.suc n *' i

  _⊔_ : ℤ -> ℤ -> ℤ
  :- m ⊔ :- n = :- (N._⊓_ m n)
  :- _ ⊔ :0   = :0
  :- _ ⊔ :+ n = :+ n
  :0   ⊔ :- _ = :0
  :0   ⊔ :0   = :0
  :0   ⊔ :+ n = :+ n
  :+ m ⊔ :- _ = :+ m
  :+ m ⊔ :0   = :+ m
  :+ m ⊔ :+ n = :+ (N._⊔_ m n)

  _⊓_ : ℤ -> ℤ -> ℤ
  :- m ⊓ :- n = :- (N._⊔_ m n)
  :- m ⊓ :0   = :- m
  :- m ⊓ :+ _ = :- m
  :0   ⊓ :- n = :- n
  :0   ⊓ :0   = :0
  :0   ⊓ :+ _ = :0
  :+ _ ⊓ :- n = :- n
  :+ _ ⊓ :0   = :0
  :+ m ⊓ :+ n = :+ (N._⊓_ m n)

  -- show : ℤ -> String
  -- show (:- n) = "-" ++ ...
  -- show :0     = "0"
  -- show (:+ n) = ...
