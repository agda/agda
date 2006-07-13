
module Example where

data Size : Set where
  empty	   : Size
  nonempty : Size
  whatever : Size

data Nat : Set where
  zero : Nat
  suc  : Nat -> Nat

data List (A:Set) : Set where
  nil  : List A
  (::) : A -> List A -> List A

data Monad (M:Set -> Set) : Set1 where
  monad : Monad M

postulate
  build : {M:Set -> Set} -> Monad M -> {C:Size -> Set} -> (A:Set) ->
	  (A -> C nonempty) ->
	  ((n:Size) -> List (C n) -> M (List A)) ->
	  List A -> M (C whatever)

test : (A:Set) -> Nat
test A = build monad A (\x -> x) (\n xs -> xs) nil

