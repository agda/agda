{-# OPTIONS --copatterns #-}
module DataRecordCoinductive where

data ⊥ : Set where
record ⊤ : Set where
  constructor tt

module Stream where

  mutual

    data Stream (A : Set) : Set where
      cons : Cons A → Stream A

    -- since Cons is coinductive, we are creating streams
    record Cons (A : Set) : Set where
      coinductive
      constructor _∷_
      field head : A
            tail : Stream A

  open Cons

  mutual

    repeat : {A : Set}(a : A) → Stream A
    repeat a = cons (repeat' a)

    repeat'  : {A : Set}(a : A) → Cons A
    head (repeat' a) = a
    tail (repeat' a) = repeat a

  -- should not termination check: coconstructors are not size preserving
  consume : {A : Set} → Stream A → ⊥
  consume (cons (x ∷ xs)) = consume xs

  loop : ⊥
  loop = consume (repeat tt)
