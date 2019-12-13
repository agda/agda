module Forcing3 where

open import Common.Nat renaming (zero to Z; suc to S)
open import Common.IO
open import Common.Unit

data _×_ (A B : Set) : Set where
  _,_ : A → B → A × B

data P {A B : Set} : A × B → Set where
  _,_ : (x : A) (y : B) → P (x , y)

data Q {A : Set} : A × A → Set where
  [_] : (x : A) → Q (x , x)

test : let t : Set
           t = (Nat × Nat) × Nat
         in (q : t × t) → Q q → Nat
test ._ [ (Z       , Z  ) , Z ]  = Z
test ._ [ (Z       , S l) , m ]  = S l + m
test ._ [ (S Z     , Z  ) , m ]  = S m
test ._ [ (S Z     , S l) , m ]  = S Z + m + l
test ._ [ (S (S n) , l  ) , m ]  = S (S n) + m + l
test ._ [ (n       , l  ) , m ]  = m

main : IO Unit
main = let tTyp : Set
           tTyp = (Nat × Nat) × Nat
           t0 : tTyp
           t0 = (0 , 0) , 0
           t1 : tTyp
           t1 = (0 , 1) , 2
           t2 : tTyp
           t2 = (1 , 0) , 3
           t3 : tTyp
           t3 = (1 , 4) , 5
           t4 : tTyp
           t4 = (3 , 2) , 10
           t5 : tTyp
           t5 = (0 , 0) , 4
           pn : tTyp → IO Unit
           pn t = printNat (test (t , t) [ t ])
        in pn t0 ,, -- 0
           pn t1 ,, -- 3
           pn t2 ,, -- 4
           pn t3 ,, -- 9
           pn t4 ,, -- 15
           pn t5 ,, -- 4
           return unit
