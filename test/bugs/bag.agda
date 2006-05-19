module Top where

module Prelude where

  data Bool : Set where
    True  : Bool
    False : Bool

  data Pair (a, b : Set) : Set where
    pair : a -> b -> Pair a b

  fst : {a, b : Set} -> Pair a b -> a
  fst {a} {b} (pair x y) = x

  snd : {a, b : Set} -> Pair a b -> b
  snd {a} {b} (pair x y) = y

  data Either (a, b : Set) : Set where
    left  : a -> Either a b
    right : b -> Either a b

  data Absurd : Set where

  data Not (a : Set) : Set where
    not : (a -> Absurd) -> Not a

  -- Not : Set -> Set
  -- Not a = a -> Absurd

module Equiv where

  open Prelude

  data Equiv (a : Set) : Set1 where
    equiv :  ((==) : a -> a -> Set)
          -> (refl  : (x : a) -> x == x)
          -> (sym   : (x, y : a) -> x == y -> y == x)
          -> (trans : (x, y, z : a) -> x == y -> y == z -> x == z)
          -> Equiv a

  rel : {a : Set} -> Equiv a -> (a -> a -> Set)
  rel {a} (equiv (==) _ _ _) = (==)

  data Decidable {a : Set} ((==) : a -> a -> Set) : Set where
    dec : ((x, y : a) -> Either (x == y) (Not (x == y))) -> Decidable (==)

  data DecidableEquiv (a : Set) : Set1 where
    decEquiv : (eq : Equiv a) -> Decidable (rel eq) -> DecidableEquiv a

  postulate
    decRel : {a : Set} -> DecidableEquiv a -> (a -> a -> Bool)

module Nat where

  data Nat : Set where
    zero : Nat
    suc  : Nat -> Nat

  one : Nat
  one = suc zero

  (+) : Nat -> Nat -> Nat
  zero  + n = n
  suc m + n = suc (m + n)

module List where

  data List (a : Set) : Set where
    nil : List a
    (::) : a -> List a -> List a

module Bag where

  open Prelude
  open Equiv
  open Nat
  open List

  abstract

    Bag : Set -> Set
    Bag a = List (Pair Nat a)

    empty : {a : Set} -> Bag a
    empty {a} = nil

    private
      lookup' :  {a : Set} -> Nat -> a -> Bag a -> Bool -> Pair Nat (Bag a)
              -> Pair Nat (Bag a)
      lookup' {a} n _ b True  _            = pair n b
      lookup' {a} n y b False (pair n' b') = pair n' (pair n y :: b')

    lookup : {a : Set} -> DecidableEquiv a -> a -> Bag a -> Pair Nat (Bag a)
    lookup {a} eq x nil             = pair zero nil
    lookup {a} eq x (pair n y :: b) =
      lookup' n y b (decRel eq x y) (lookup eq x b)

    private
      insert' : {a : Set} -> a -> Pair Nat (Bag a) -> Bag a
      insert' {a} x (pair n b) = pair (suc n) x :: b

    insert : {a : Set} -> DecidableEquiv a -> a -> Bag a -> Bag a
    insert {a} eq x b = insert' x (lookup eq x b)

    -- bagElim should not type check, but it shouldn't crash the type
    -- checker either:

    -- agda: Prelude.(!!): index too large

    bagElim
      :  {a : Set}
      -> ((==) : DecidableEquiv a)
      -> (P : Bag a -> Set)
      -> P empty
      -> ((x : a) -> (b : Bag a) -> P b -> P (insert (==) x b))
      -> (b : Bag a)
      -> P b
    bagElim {a} (==) P e i nil                         = e
    bagElim {a} (==) P e i (pair (suc zero) x :: b)    =
      i x b (bagElim (==) P e i b)
    bagElim {a} (==) P e i (pair (suc (suc n)) x :: b) =
      i x (pair (suc n) x :: b) (bagElim (==) P e i (pair (suc n) x :: b))

