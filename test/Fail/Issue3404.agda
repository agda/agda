-- Andreas, 2018-11-23, issue #3404, regression in Agda 2.5.4
--
-- The positivity checker judged postulates in mutual blocks
-- as constants, since it found no uses of its arguments.
--
-- The natural cure is to not unleash the positivity checker
-- onto things that do not have a definition, such as postulates.

open import Agda.Builtin.Nat
open import Agda.Builtin.Equality

trans : {A : Set} {a b c : A} → a ≡ b → b ≡ c → a ≡ c
trans refl refl = refl

module UnsolvedMeta where

  postulate        A : Set
  mutual postulate B : A → Set       -- Problem WAS: B is judged constant
  postulate        f : (a : A) → B a

  g : (a : A) → B a
  g a = f _  -- WAS: yellow

  -- Should solve.

-- False golfing:

mutual
  postulate
    2^  : Nat → Nat  -- If this function is deemed constant,
    2^0 : 1 ≡ 2^ 0   -- then these equalities can be composed.
    2^1 : 2^ 1 ≡ 2

bad : 1 ≡ 2
bad = trans 2^0 2^1

-- Should fail with error like:
--
-- 1 != 0 of type Nat
-- when checking that the expression 2^1 has type 2^ 0 ≡ 2
