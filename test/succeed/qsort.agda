{-# OPTIONS --no-termination-check #-}

module qsort where

  _o_ : {a : Set} -> {b : Set} -> {c : Set} -> (b -> c) -> (a -> b) -> a -> c
  f o g = \x -> f (g x)

  data Bool : Set where
    true  : Bool
    false : Bool

  not : Bool -> Bool
  not true  = false
  not false = true

  if_then_else_ : {a : Set} -> Bool -> a -> a -> a
  if true  then x else _ = x
  if false then _ else y = y

  data List (a : Set) : Set where
    nil  : List a
    _::_ : a -> List a -> List a

  listrec : {a : Set} -> List a -> (a -> List a -> List a) -> List a -> List a
  listrec e _  nil    = e
  listrec e b (x :: xs) = b x (listrec e b xs)

  filter : {a : Set} -> (a -> Bool) -> List a -> List a
  filter f = listrec nil (\x ih -> if (f x) then (x :: ih) else ih)

  _++_ : {a : Set} -> List a -> List a -> List a
  nil ++ ys = ys
  (x :: xs) ++ ys = x :: (xs ++ ys)

  data Nat : Set where
    zero : Nat
    succ : Nat -> Nat

  _+_ : Nat -> Nat -> Nat
  zero   + m = m
  succ n + m = succ (n + m)

  _*_ : Nat -> Nat -> Nat
  zero   * m = zero
  succ n * m = m + (n * m)

  one : Nat
  one = succ zero

  fact : Nat -> Nat
  fact  zero    = one
  fact (succ n) = succ n * fact n 

  _<_ : Nat -> Nat -> Bool
  zero     < zero     = false
  zero     < n        = true
  n        < zero     = false
  (succ n) < (succ m) = n < m

  --

  qsort : {a : Set} -> (a -> a -> Bool) -> List a -> List a
  qsort f nil       = nil
  qsort f (x :: xs) = (qsort f (filter (not o (f x)) xs)) ++
                    (x :: (qsort f (filter (f x) xs)))
