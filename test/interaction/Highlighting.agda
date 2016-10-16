module Highlighting where

Set-one : Set₂
Set-one = Set₁

record R (A : Set) : Set-one where
  constructor con

  field X : Set

  F : Set → Set → Set
  F A B = B

  field P : F A X → Set

  -- highlighting of non-terminating definition
  Q : F A X → Set
  Q = Q

postulate P : _

open import Highlighting.M

data D (A : Set) : Set-one where
  d : let X = D in X A

postulate _+_ _×_ : Set → Set → Set

infixl 4 _×_ _+_
  -- Issue #2140: the operators should be highlighted also in the
  -- fixity declaration.
