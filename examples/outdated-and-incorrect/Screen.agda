
module Screen where

import Data.Nat
import Data.Bool
import Data.List
import Logic.Base

open Data.Bool
open Data.List
open Data.Nat
open Logic.Base

-- Ranges -----------------------------------------------------------------

data Range : Set where
  range : Nat -> Nat -> Range

inRange : Range -> Nat -> Bool
inRange (range lo hi) x = lo ≤ x && x ≤ hi

low : Range -> Nat
low (range lo _) = lo

high : Range -> Nat
high (range _ hi) = hi

size : Range -> Nat
size (range lo hi) = suc hi - lo

enumerate : Range -> List Nat
enumerate (range lo hi) = enum lo hi
  where
    list : Nat -> Nat -> List Nat
    list _ 0       = []
    list k (suc n) = k :: list (suc k) n

    enum : Nat -> Nat -> List Nat
    enum lo hi = map (_+_ lo) (list 0 (suc hi - lo))

-- The screen example -----------------------------------------------------

xRange : Range
xRange = range 0 79

yRange : Range
yRange = range 0 24

screenRange : Range
screenRange = range 0xb8000 0xb87ff

-- Converting (x,y) to addr

plot : Nat -> Nat -> Nat
plot x y = low screenRange + x + size xRange * y

-- The property

forAll : Range -> (Nat -> Bool) -> Bool
forAll r p = foldr (\n b -> p n && b) true (enumerate r)

prop : Bool
prop = forAll xRange \x ->
       forAll yRange \y ->
       inRange screenRange (plot x y)

proof : IsTrue prop
proof = tt

