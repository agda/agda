
module DataRecordInductive where

module NotMutual where

  record Nil (A : Set) : Set where
    constructor []

  record Cons (A X : Set) : Set where
    constructor _∷_
    field head : A
          tail : X
  open Cons

  data List (A : Set) : Set where
    nil  : Nil A  → List A
    cons : Cons A (List A) → List A

  -- works
  module Constr where

    map : {A B : Set} → (A → B) → List A → List B
    map f (nil   [])      = nil []
    map f (cons (x ∷ xs)) = cons (f x ∷ map f xs)

  -- works, since projections are size preserving
  module Proj where

    map : {A B : Set} → (A → B) → List A → List B
    map f (nil   _) = nil []
    map f (cons  p) = cons (f (head p) ∷ map f (tail p))

module Mutual where

  mutual

    data List (A : Set) : Set where
      nil  : Nil A  → List A
      cons : Cons A → List A

    record Nil (A : Set) : Set where
      constructor []

    -- since Cons is inductive, we are not creating colists
    record Cons (A : Set) : Set where
      inductive
      constructor _∷_
      field head : A
            tail : List A

  open Cons

  -- works
  module Constr where

    map : {A B : Set} → (A → B) → List A → List B
    map f (nil   [])      = nil []
    map f (cons (x ∷ xs)) = cons (f x ∷ map f xs)

  -- works, since projections of an inductive record are size-preserving
  module Proj where

    map : {A B : Set} → (A → B) → List A → List B
    map f (nil   _) = nil []
    map f (cons  p) = cons (f (head p) ∷ map f (tail p))
