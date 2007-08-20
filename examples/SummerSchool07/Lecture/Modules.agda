{-

          Types Summer School 2007

                 Bertinoro
             Aug 19 - 31, 2007


                   Agda

                Ulf Norell

-}

-- Let's have a closer look at the module system

module Modules where

{-

  Importing and opening modules

-}

-- You can import a module defined in a different file.
import Nat

-- This will bring the module into scope and allows you to
-- access its contents using qualified names.
plusTwo : Nat.Nat -> Nat.Nat
plusTwo n = Nat._+_ n 2

-- To bring everything from a module into scope you can open
-- the module.
open Nat

z : Nat
z = zero

-- There's also a short-hand to import and open at the same time
open import Bool

_&&_ : Bool -> Bool -> Bool
x && y = if x then y else false

-- Sometimes it's nice to be able to control what is brought
-- into scope when you open a module. There are three modifiers
-- that affect this: using, hiding and renaming.

module DifferentWaysOfOpeningNat where

  -- nothing but Nat
  open Nat using (Nat)

  -- everything but zero
  open Nat hiding (zero)

  -- everything, but zero and suc under different names
  open Nat renaming (zero to ZZ; suc to S_S)

  two : Nat
  two = S S zero S S

  -- you can combine using or hiding with renaming, but not using
  -- with hiding (for obvious reasons).

-- To re-export something opened use the public modifier.
module A where
  open Nat public using (Nat)

N = A.Nat -- now Nat is a visible name in module A

{-

  Parameterised modules

-}

-- A very useful feature is parameterised modules.

data Vec (A : Set) : Nat -> Set where
  []   : Vec A 0
  _::_ : {n : Nat} -> A -> Vec A n -> Vec A (suc n)

infixr 40 _::_

module Sort {A : Set}(_≤_ : A -> A -> Bool) where

  insert : {n : Nat} -> A -> Vec A n -> Vec A (suc n)
  insert x [] = x :: []
  insert x (y :: ys) = if x ≤ y
                       then x :: y :: ys
                       else y :: insert x ys

  sort : {n : Nat} -> Vec A n -> Vec A n
  sort []        = []
  sort (x :: xs) = insert x (sort xs)

_≤_ : Nat -> Nat -> Bool
zero  ≤ m     = true
suc n ≤ zero  = false
suc n ≤ suc m = n ≤ m

-- When used directly, functions from parameterised modules
-- take the parameters as extra arguments.
test = Sort.sort _≤_ (6 :: 2 :: 0 :: 4 :: [])

-- But, you can also apply the entire module to its arguments.
-- Let's open the new module while we're at it.
open module SortNat = Sort _≤_

test' = sort (3 :: 2 :: 4 :: 0 :: [])

{-

  Local definitions

-}

data _==_ {A : Set}(x : A) : A -> Set where
  refl : x == x

subst : {A : Set}(C : A -> Set){x y : A} -> x == y -> C x -> C y
subst C refl cx = cx

cong : {A B : Set}(f : A -> B){x y : A} -> x == y -> f x == f y
cong f refl = refl

lem₁ : (n : Nat) -> n + 0 == n
lem₁ zero    = refl
lem₁ (suc n) = cong suc (lem₁ n)

lem₂ : (n m : Nat) -> n + suc m == suc n + m
lem₂ n  zero   = refl
lem₂ n (suc m) = cong suc (lem₂ n m)

{-

  What's next?

-}

-- The final thing on the agenda is records.

-- Move on to: Records.agda
