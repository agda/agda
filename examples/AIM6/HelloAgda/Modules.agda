{-

        Agda Implementors' Meeting VI

                  Göteborg
             May 24 - 30, 2007


                Hello Agda!

                Ulf Norell

-}

-- Let's have a closer look at the module system

module Modules where

{-

  Importing and opening modules

-}

-- You can import a module defined in a different file.
import Naturals

-- This will bring the module into scope and allows you to
-- access its contents using qualified names.
plusTwo : Naturals.Nat -> Naturals.Nat
plusTwo n = Naturals._+_ n 2

-- To bring everything from a module into scope you can open
-- the module.
open Naturals

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
  open Naturals using (Nat)

  -- everything but zero
  open Naturals hiding (zero)

  -- everything, but zero and suc under different names
  open Naturals renaming (zero to ZZ; suc to S_S)

  two : Nat
  two = S S ZZ S S

  -- you can combine using or hiding with renaming, but not using
  -- with hiding (for obvious reasons).

-- To re-export something opened use the public modifier.
module A where
  open Naturals public using (Nat)

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
lem₂  zero   m = refl
lem₂ (suc n) m = cong suc (lem₂ n m)

-- You can define things locally to a function clause
reverse : {A : Set}{n : Nat} -> Vec A n -> Vec A n
reverse {A} = \xs -> subst (Vec A) (lem₁ _) (rev xs [])
  where
    rev : {n m : Nat} -> Vec A n -> Vec A m -> Vec A (n + m)
    rev []              ys = ys
    rev (_::_ {n} x xs) ys = subst (Vec A) (lem₂ n _)
                                   (rev xs (x :: ys))

-- More precisely, each clause can have one local module. In the
-- example above we didn't bother naming the module. We could've
-- said
reverse' : {A : Set}{n : Nat} -> Vec A n -> Vec A n
reverse' {A}{n} = \xs -> subst (Vec A) (lem₁ n) (rev xs [])
  module Rev where
    rev : {m p : Nat} -> Vec A m -> Vec A p -> Vec A (m + p)
    rev []              ys = ys
    rev (_::_ {n} x xs) ys = subst (Vec A) (lem₂ n _)
                                   (rev xs (x :: ys))

-- Now we can access the local function from inside the module Rev.
-- Variables bound in the left hand side of the clause become
-- parameters to the module, so since the implicit n argument to
-- reverse' is bound implicitly there's an extra argument of type
-- Nat which isn't used.

test'' = Rev.rev {_}{0} (4 :: 3 :: 2 :: []) (5 :: 6 :: [])

{-

  What's next?

-}

-- The final thing on the agenda is records.

-- Move on to: Records.agda
