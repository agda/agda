-- Andreas, 2017-11-12, issue #2803

-- Problem: names of hidden variable patterns
-- can get lost during case splitting.

-- They actually get lost already during lhs type checking,
-- but it is noticed only when printed back to the user
-- during case splitting.

-- {-# OPTIONS -v tc.lhs:40 #-}

record HFun (A B : Set) : Set where
  field apply : {a : A} → B

postulate A : Set

test : HFun A (A → A)
HFun.apply test {β} = {!!} -- C-c C-c

-- YIELDS:
-- HFun.apply test {a} x = ?

-- EXPECTED:
-- HFun.apply test {β} x = ?

open import Agda.Builtin.Bool

test' : {a b : Bool} → Bool → Bool
test' {b = z} x = {!x!}

-- Splitting on x should yield

-- test {b = z} false = {!!}
-- test {b = z} true = {!!}
