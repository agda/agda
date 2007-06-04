-- simulating streams by Nat -> A

module Stream where

data Bool : Set where
    true  : Bool
    false : Bool

if_then_else_ : forall {A} -> Bool -> A -> A -> A
if true  then t else e = t
if false then t else e = e

data Nat : Set where
    zero : Nat
    succ : Nat -> Nat

Stream : Set -> Set
Stream A = Nat -> A

_::_ : forall {A} -> A -> Stream A -> Stream A
_::_ a as zero     = a
_::_ a as (succ n) = as n

map : forall {A B} -> (A -> B) -> Stream A -> Stream B
map f as n = f (as n)

head : forall {A} -> Stream A -> A
head as = as zero

tail : forall {A} -> Stream A -> Stream A
tail as n = as (succ n)

-- construct the stream a :: f a :: f (f a) :: ...

iterate : forall {A} -> (A -> A) -> A -> Stream A
iterate f a zero = a
iterate f a (succ n) = iterate f (f a) n

zipWith : forall {A B C} -> (A -> B -> C) -> Stream A -> Stream B -> Stream C
zipWith f as bs n = f (as n) (bs n)

-- merge with with
merge : forall {A} -> (A -> A -> Bool) -> Stream A -> Stream A -> Stream A
merge le as bs with le (head as) (head bs)
merge le as bs | true  = head as :: merge le (tail as) bs
merge le as bs | false = head bs :: merge le as (tail bs)

{-
-- without with
merge' : forall {A} -> (A -> A -> Bool) -> Stream A -> Stream A -> Stream A
merge' le as bs = if le (head as) (head bs)
                  then (head as :: merge' le (tail as) bs)
                  else (head bs :: merge' le as (tail bs))
-}

-- BOTH VARIANTS OF MERGE ARE NOT STRUCTURALLY RECURSIVE

