-- Test tagged array encoding of constructors for the JS backend.
-- Covers: pure enums, mixed-arity constructors, default (catch-all) branches,
-- nested case on two tagged-array types, interaction with builtin types.

module TaggedArrays where

open import Common.Nat
open import Common.IO
open import Common.Unit
open import Common.String

------------------------------------------------------------------------
-- 1. Pure enum: 6 nullary constructors (all tags, no fields)

data Color : Set where
  red green blue yellow cyan magenta : Color

showColor : Color -> String
showColor red     = "red"
showColor green   = "green"
showColor blue    = "blue"
showColor yellow  = "yellow"
showColor cyan    = "cyan"
showColor magenta = "magenta"

------------------------------------------------------------------------
-- 2. Mixed-arity constructors (0, 1, 2, 3 fields)

data Shape : Set where
  dot    : Shape
  circle : Nat -> Shape
  rect   : Nat -> Nat -> Shape
  tri    : Nat -> Nat -> Nat -> Shape

perimeter : Shape -> Nat
perimeter dot          = 0
perimeter (circle r)   = r * 6
perimeter (rect w h)   = (w + h) * 2
perimeter (tri a b c)  = a + b + c

------------------------------------------------------------------------
-- 3. Default branch (catch-all on tagged-array type)

isWarm : Color -> String
isWarm red     = "warm"
isWarm yellow  = "warm"
isWarm magenta = "warm"
isWarm _       = "cool"

------------------------------------------------------------------------
-- 4. Nested case on two different tagged-array types

describe : Color -> Shape -> String
describe red   (circle _) = "red circle"
describe blue  dot         = "blue dot"
describe green (rect _ _)  = "green rect"
describe _     _           = "other"

------------------------------------------------------------------------
-- 5. Tagged-array type containing builtin Nat, case on both

data Bucket : Set where
  empty  : Bucket
  single : Nat -> Bucket
  pair   : Nat -> Nat -> Bucket

bucketSum : Bucket -> Nat
bucketSum empty      = 0
bucketSum (single x) = x
bucketSum (pair x y) = x + y

addToBucket : Nat -> Bucket -> Bucket
addToBucket n empty      = single n
addToBucket n (single x) = pair n x
addToBucket n (pair x y) = pair n (x + y)

------------------------------------------------------------------------
-- 6. Nested tagged arrays: tagged-array type as field of another

data Tree : Set where
  leaf : Nat -> Tree
  node : Tree -> Tree -> Tree

sumTree : Tree -> Nat
sumTree (leaf n)   = n
sumTree (node l r) = sumTree l + sumTree r

------------------------------------------------------------------------

main : IO Unit
main =
  -- 1. Pure enum
  putStrLn (showColor red) ,,
  putStrLn (showColor blue) ,,
  putStrLn (showColor magenta) ,,
  -- 3. Default branch
  putStrLn (isWarm red) ,,
  putStrLn (isWarm green) ,,
  putStrLn (isWarm cyan) ,,
  putStrLn (isWarm magenta) ,,
  -- 2. Mixed arity
  printNat (perimeter dot) ,,
  putStrLn "" ,,
  printNat (perimeter (circle 5)) ,,
  putStrLn "" ,,
  printNat (perimeter (rect 3 7)) ,,
  putStrLn "" ,,
  printNat (perimeter (tri 3 4 5)) ,,
  putStrLn "" ,,
  -- 4. Nested case on two tagged-array types
  putStrLn (describe red (circle 1)) ,,
  putStrLn (describe blue dot) ,,
  putStrLn (describe green (rect 2 3)) ,,
  putStrLn (describe yellow (tri 1 2 3)) ,,
  -- 5. Tagged-array + builtin Nat
  printNat (bucketSum empty) ,,
  putStrLn "" ,,
  printNat (bucketSum (single 42)) ,,
  putStrLn "" ,,
  printNat (bucketSum (pair 10 20)) ,,
  putStrLn "" ,,
  printNat (bucketSum (addToBucket 5 empty)) ,,
  putStrLn "" ,,
  printNat (bucketSum (addToBucket 5 (single 3))) ,,
  putStrLn "" ,,
  printNat (bucketSum (addToBucket 5 (pair 3 7))) ,,
  putStrLn "" ,,
  -- 6. Nested tagged arrays (tree)
  printNat (sumTree (leaf 1)) ,,
  putStrLn "" ,,
  printNat (sumTree (node (leaf 2) (leaf 3))) ,,
  putStrLn "" ,,
  printNat (sumTree (node (node (leaf 1) (leaf 2)) (node (leaf 3) (leaf 4)))) ,,
  putStrLn "" ,,
  return unit
