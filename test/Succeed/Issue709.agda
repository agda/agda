{-# OPTIONS --sized-types #-}
-- {-# OPTIONS --termination-depth=2 #-} -- not necessary!
-- {-# OPTIONS -v tc.size.solve:60 --show-implicit #-}
-- {-# OPTIONS -v term:5 #-}
module Issue709 where

open import Common.Size

data Bool : Set where true false : Bool

postulate
  A : Set
  _<=_ : A → A → Bool

data List {i : Size} : Set where
  []   : List
  cons : (j : Size< i) → A → List {j} → List {i}

module If where

  if_then_else_ : {A : Set} → Bool → A → A → A
  if true  then t else e = t
  if false then t else e = e

  merge : ∀ {i j} → List {i} → List {j} → List -- {∞}
  merge {i} {j} []             ys  = ys
  merge {i} {j} (cons i' x xs) []  = cons _ x xs
  merge {i} {j} (cons i' x xs) (cons j' y ys) =
    if x <= y
    then cons _ x (merge xs (cons _ y ys))
    else cons _ y (merge (cons _ x xs) ys)

module Succeeds where

  merge : ∀ {i j} → List {i} → List {j} → List
  merge          []            ys  = ys
  merge         (cons i' x xs) []  = cons _ x xs
  merge {i} {j} (cons i' x xs) (cons j' y ys) with x <= y
  ... | true  = cons _ x (merge {i'} {j} -- removing this implicit application makes it not termination check
                                xs (cons _ y ys))
  ... | false = cons _ y (merge (cons _ x xs) ys)

module NeedsTerminationDepthTwo where

  merge : ∀ {i j} → List {i} → List {j} → List
  merge          []            ys  = ys
  merge          (cons j x xs) []  = cons _ x xs
  merge {i} {i'} (cons j x xs) (cons j' y ys) with x <= y
  ... | true  = cons _ x (merge xs (cons _ y ys))
  ... | false = cons _ y (merge (cons _ x xs) ys)
