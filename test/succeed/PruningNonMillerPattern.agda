-- {-# OPTIONS -v tc.meta:100 #-}
-- Andreas, 2011-04-20
-- see Abel Pientka TLCA 2011
module PruningNonMillerPattern where

data _≡_ {A : Set}(a : A) : A -> Set where
  refl : a ≡ a

data Nat : Set where
  zero : Nat
  suc  : Nat -> Nat

-- bad variable y in head position
test : let X : Nat -> Nat -> Nat
           X = _
           Y : Nat -> Nat -> Nat
           Y = _
       in  (C : Set) ->
           (({x y : Nat} -> X x x ≡ suc (Y x y)) ->
            ({x y : Nat} -> Y x x ≡ x)           ->
            ({x y : Nat} -> X (Y x y) y ≡ X x x) -> C) -> C
test C k = k refl refl refl
{- none of these equations is immediately solvable.  However,
   from 1. we deduce that Y does not depend on its second argument, thus
   from 2. we solve Y x y = x, and then
   eqn. 3. simplifies to X x y = X x x, thus, X does not depend on its second arg,
   we can then solve using 1.  X x y = suc x
-}

-- a variant, where pruning is even triggered from a non-pattern
test' : let X : Nat -> Nat -> Nat
            X = _
            Y : Nat -> Nat -> Nat
            Y = _
        in  (C : Set) ->
            (({x y : Nat} -> X x (suc x) ≡ suc (Y x y)) ->  -- non-pattern lhs
             ({x y : Nat} -> Y x x ≡ x)           ->
             ({x y : Nat} -> X (Y x y) y ≡ X x x) -> C) -> C
test' C k = k refl refl refl

-- another variant, where the pruned argument does not have an offending
-- variable in the head, but in a non-eliminateable position
-- (argument to a datatype)

data Sing {A : Set} : A → Set where
  sing : (x : A) -> Sing x

-- bad rigid under a data type constructor
test2 : let X : Nat -> Nat -> Nat
            X = _
            Y : Nat → Set -> Nat
            Y = _
        in  (C : Set) ->
            (({x y : Nat} -> X x x ≡ suc (Y x (Sing (suc y)))) ->
             ({x y : Nat} -> Y x (Sing x) ≡ x)           ->
             ({x y : Nat} -> X (Y x (Sing y)) y ≡ X x x) -> C) -> C
test2 C k = k refl refl refl

T : Nat → Set
T zero    = Nat
T (suc _) = Nat → Nat

-- bad rigid y under a Pi type constructor
test3 : let X : Nat -> Nat -> Nat
            X = _
            Y : Nat → Set -> Nat
            Y = _
        in  (C : Set) ->
            (({x y : Nat} -> X x x ≡ suc (Y x (T y -> T y))) ->
             ({x y : Nat} -> Y x (Sing x) ≡ x)           ->
             ({x y : Nat} -> X (Y x (Sing y)) y ≡ X x x) -> C) -> C
test3 C k = k refl refl refl

-- bad rigid y in head position under a lambda
test4 : let X : Nat -> Nat -> Nat
            X = _
            Y : Nat → (Nat → Nat) -> Nat
            Y = _
        in  (C : Set) ->
            ((∀ {x : Nat} {y : Nat → Nat} -> X x x ≡ suc (Y x (λ k → y zero))) ->
             (∀ {x : Nat} {y : Nat → Nat} -> Y x (λ k → y zero) ≡ x)           ->
             (∀ {x : Nat} {y : Nat } -> X (Y x (λ k → y)) y ≡ X x x) -> C) -> C
test4 C k = k refl refl refl

-- bad variable in irrelevant position
test5 : let X : Nat -> Nat -> Nat
            X = _
            Y : Nat -> .Nat -> Nat
            Y = _
        in  (C : Set) ->
            (({x y : Nat} -> X x (suc x) ≡ suc (Y x (suc y))) ->  -- non-pattern lhs
             ({x y : Nat} -> Y x x ≡ x)           ->
             ({x y : Nat} -> X (Y x (suc y)) y ≡ X x x) -> C) -> C
test5 C k = k refl refl refl
