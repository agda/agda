-- Issue #2791, reported by Ulf 2017-10-05
-- Reported fixed by Victor 2018-08-11

open import Agda.Builtin.Nat
open import Agda.Builtin.Bool
open import Agda.Builtin.Equality

IF : Bool → Set → Set → Set
IF true  X Y = X
IF false X Y = Y

postulate
  F : (A : Set) (x : A) (B : Set) (y : B) → Set

mutual
  ?b : Bool
  ?b = _

  IFb = IF ?b Nat Bool

  ?X : IFb
  ?X = _

  ?Y : Nat
  ?Y = _

  foo : F Bool true Nat ?Y ≡ F IFb ?X IFb ?X
  foo = refl

-- ?Y gets solved with 'true'
error : ?Y + 1 ≡ 3
error = refl

-- Expected failure:

-- Nat != Bool of type Set
-- when checking that the expression refl has type
-- F Bool true Nat ?Y ≡ F IFb ?X IFb ?X
