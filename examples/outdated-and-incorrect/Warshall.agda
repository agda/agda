
module Warshall
  (X   : Set)
  ((≤) : X -> X -> Prop)
  -- and axioms...
  where

id : {A:Set} -> A -> A
id x = x

(∘) : {A B C:Set} -> (B -> C) -> (A -> B) -> A -> C
f ∘ g = \x -> f (g x)

-- Natural numbers --------------------------------------------------------

data Nat : Set where
  zero : Nat
  suc  : Nat -> Nat

(+) : Nat -> Nat -> Nat
zero  + m = m
suc n + m = suc (n + m)

-- Finite sets ------------------------------------------------------------

data Zero : Set where

data Suc (A:Set) : Set where
  fzero_ : Suc A
  fsuc_  : A -> Suc A

mutual

  data Fin (n:Nat) : Set where
    finI : Fin_ n -> Fin n

  Fin_ : Nat -> Set
  Fin_  zero   = Zero
  Fin_ (suc n) = Suc (Fin n)

fzero : {n:Nat} -> Fin (suc n)
fzero = finI fzero_

fsuc : {n:Nat} -> Fin n -> Fin (suc n)
fsuc i = finI (fsuc_ i)

finE : {n:Nat} -> Fin n -> Fin_ n
finE (finI i) = i

infixr 15 ::

-- Vectors ----------------------------------------------------------------

data Nil : Set where
  nil_ : Nil

data Cons (Xs:Set) : Set where
  cons_ : X -> Xs -> Cons Xs

mutual

  data Vec (n:Nat) : Set where
    vecI : Vec_ n -> Vec n

  Vec_ : Nat -> Set
  Vec_  zero   = Nil
  Vec_ (suc n) = Cons (Vec n)

nil : Vec zero
nil = vecI nil_

(::) : {n:Nat} -> X -> Vec n -> Vec (suc n)
x :: xs = vecI (cons_ x xs)

vecE : {n:Nat} -> Vec n -> Vec_ n
vecE (vecI xs) = xs

vec : (n:Nat) -> X -> Vec n
vec  zero   _ = nil
vec (suc n) x = x :: vec n x

map : {n:Nat} -> (X -> X) -> Vec n -> Vec n
map {zero}  f (vecI nil_)	  = nil
map {suc n} f (vecI (cons_ x xs)) = f x :: map f xs

(!) : {n:Nat} -> Vec n -> Fin n -> X
(!) {suc n} (vecI (cons_ x _ )) (finI fzero_)    = x
(!) {suc n} (vecI (cons_ _ xs)) (finI (fsuc_ i)) = xs ! i

upd : {n:Nat} -> Fin n -> X -> Vec n -> Vec n
upd {suc n} (finI fzero_)    x (vecI (cons_ _ xs)) = x :: xs
upd {suc n} (finI (fsuc_ i)) x (vecI (cons_ y xs)) = y :: upd i x xs

tabulate : {n:Nat} -> (Fin n -> X) -> Vec n
tabulate {zero}  f = nil
tabulate {suc n} f = f fzero :: tabulate (\x -> f (fsuc x))

postulate
  (===) : {n:Nat} -> Vec n -> Vec n -> Prop


module Proof
    (F : {n:Nat} -> Vec n -> Vec n)
    -- and axioms...
    where

  stepF : {n:Nat} -> Fin n -> Vec n -> Vec n
  stepF i xs = upd i (F xs ! i) xs

  unsafeF' : {n:Nat} -> Nat -> Vec (suc n) -> Vec (suc n)
  unsafeF' zero    = id
  unsafeF' (suc m) = unsafeF' m ∘ stepF fzero

  unsafeF : {n:Nat} -> Vec n -> Vec n
  unsafeF {zero}  = id
  unsafeF {suc n} = unsafeF' (suc n)

  thm : {n:Nat} -> (xs:Vec n) -> F xs === unsafeF xs
  thm = ?

