{-# OPTIONS --erasure --erase-record-parameters #-}

module _ where

module ErasedField where

  record R (A : Set) : Set where
    field
      f : A

  test : {@0 A : Set} → R A → A
  test = R.f


module ErasedDefinition where

  postulate A : Set
  postulate a : A

  record R (x : A) : Set where
    y : A
    y = a

  f : (@0 x : A) → R x → A
  f x r = R.y {x} r

  open R {{...}}

  g : {@0 x : A} → {{R x}} → A
  g = y
