
module Bush where

data Nat : Set where
  zero : Nat
  suc  : Nat -> Nat

{-# BUILTIN NATURAL Nat #-}
{-# BUILTIN ZERO zero #-}
{-# BUILTIN SUC suc #-}

_^_ : (Set -> Set) -> Nat -> Set -> Set
(F ^ zero)  A = A
(F ^ suc n) A = F ((F ^ n) A)

data Bush (A : Set) : Set where
  leaf : Bush A
  node : A -> (Bush ^ 3) A -> Bush A

elim :
  (P : (A : Set) -> Bush A -> Set) ->
  ((A : Set) -> P A leaf) ->
  ((A : Set)(x : A)(b : (Bush ^ 3) A) ->
    P ((Bush ^ 2) A) b -> P A (node x b)) ->
  (A : Set)(b : Bush A) -> P A b
elim P l n A leaf       = l A
elim P l n A (node x b) = n A x b (elim P l n ((Bush ^ 2) A) b)

data List (A : Set) : Set where
  []   : List A
  _::_ : A -> List A -> List A

_++_ : {A : Set} -> List A -> List A -> List A
[] ++ ys = ys
(x :: xs) ++ ys = x :: (xs ++ ys)

Flatter : Set -> Set -> Set
Flatter A B = A -> List B

flatterN : {A B : Set} -> (n : Nat) ->  Flatter A B -> Flatter ((Bush ^ n) A) B
flatterN zero    f x          = f x
flatterN (suc n) f leaf       = []
flatterN (suc n) f (node x b) = flatterN n f x ++ flatterN (suc (suc (suc n))) f b

flatten : {A : Set} -> Bush A -> List A
flatten = flatterN (suc zero) (\x -> x :: [])
