-- {-# OPTIONS -v tc.meta:20  #-}

-- Andreas, 2011-04-15
-- source: Conor's post "foldl Miller magic" on the Agda list (2008)

module Issue325b where

data Nat : Set where
  zero  : Nat
  suc   : Nat -> Nat

data Vec (X : Set) : Nat -> Set where
  [] : Vec X zero
  cons : (n : Nat) -> X -> Vec X n -> Vec X (suc n)

foldl : (S : Set)(T : Nat -> Set) ->
        ((n : Nat) -> T n -> S -> T (suc n)) ->
        T zero ->
        (n : Nat) -> Vec S n -> T n
foldl S T0  f t ._ [] = t
foldl S Tsn f t ._ (cons m s ss) =
  foldl S _ -- (\ n -> Tsn (suc n))
--        (\ n -> f _) (f _ t s) _ ss
           _ (f zero t s) _ ss
--        (\ n -> f (suc n)) (f zero t s) _ ss

{- PROTOCOL:

term _43 S Tsn f t m s ss zero    := suc zero

term _43 S Tsn f t m s ss (suc n) := suc (_43 S Tsn f t m s ss n)

term _43 S Tsn f t m s ss m       := suc m

Pruning could give us:

_43 m zero    := suc zero
_43 m (suc n) := suc (_43 m n)
_43 m m       := suc m

We could then try
a) _43 x y := suc x  failing
b) _43 x y := suc y  succeeding
but this only complete in the absence of recursion.
-}
