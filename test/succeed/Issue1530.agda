-- {-# OPTIONS --show-implicit #-}
-- {-# OPTIONS -v term:20 -v term.function:30 #-}

-- Andreas, 2015-05-31, issue reported by Bruno Bianchi

module Issue1530 {A : Set}(_<=_ : A -> A -> Set) where

open import Common.List
open import Issue1530.Bound _<=_

data OList : Bound -> Set where
  nil : {b : Bound} -> OList b
  cons : {b : Bound}{x : A} -> LeB b (val x) -> OList (val x) -> OList b

forget : {b : Bound} -> OList b -> List A
forget nil = []
forget (cons {x = x} _ xs) = x ∷ forget xs

data Sorted : List A -> Set where
  empty : Sorted []
  single : (x : A) -> Sorted (x ∷ [])
  step : {x y : A}{ys : List A} -> x <= y -> Sorted (y ∷ ys) -> Sorted (x ∷ y ∷ ys)

olist-sorted : {b : Bound}(xs : OList b) -> Sorted (forget xs)
olist-sorted nil = empty
olist-sorted (cons {x = x} _ nil) = single x
olist-sorted (cons b<=x (cons (lexy x<=y) ys)) = step x<=y (olist-sorted (cons (lexy x<=y) ys))

-- should termination check

-- problem WAS: TermCheck did not *deeply* resolve constructor names on rhs in last clause.
-- TermCheck.reduceCon did not reduce the lexy on the rhs, as it was deep inside.
