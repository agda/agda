{-# OPTIONS --allow-unsolved-metas #-}
module _ where

open import Agda.Builtin.Equality

module Case₀ where

  postulate
    I : Set
    P : I → Set

  variable
    p : P _

  postulate
    D : P _ → Set
    d : D p

module Case₁ where

  postulate
    I : Set
    P : I → Set
    Q : ∀ n → P n → Set

  variable
    q : Q _ _

  postulate
    D : ∀ {p} → Q _ p → Set
    d : D q

module Case₂ where

  postulate
    I : Set
    P : I → Set
    Q : ∀ n → P n → Set

  record R n (p : P n) : Set where
    constructor c
    field
      f : Q _ p

  variable
    q : Q _ _

  data D {p} : R _ p → Set where
    d : D (c q)

module Case₃ where

  variable
    A : Set
    a : A

  record B : Set where
    id = λ x → x ≡ x
    field
      b : id a
