
module Bush where

data Nat : Set where
  zero : Nat
  suc  : Nat -> Nat

{-# BUILTIN NATURAL Nat #-}
{-# BUILTIN ZERO zero #-}
{-# BUILTIN SUC suc #-}

_+_ : Nat -> Nat -> Nat
zero  + m = m
suc n + m = suc (n + m)

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

iter :
  (P : (A : Set) -> Set) ->
  ((A : Set) -> P A) ->
  ((A : Set) -> A -> P ((Bush ^ 2) A) -> P A) ->
  (A : Set) -> Bush A -> P A
iter P l n A leaf       = l A
iter P l n A (node x b) = n A x (iter P l n ((Bush ^ 2) A) b)

data List (A : Set) : Set where
  []   : List A
  _::_ : A -> List A -> List A

_++_ : {A : Set} -> List A -> List A -> List A
[] ++ ys = ys
(x :: xs) ++ ys = x :: (xs ++ ys)

flatten : {A : Set}(n : Nat) -> (Bush ^ n) A -> List A
flatten zero    x          = x :: []
flatten (suc n) leaf       = []
flatten (suc n) (node x b) = flatten n x ++ flatten (3 + n) b
