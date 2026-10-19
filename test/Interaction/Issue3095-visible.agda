open import Agda.Builtin.Nat

foo : Nat → Nat
foo x = bar x
  where
    bar : Nat → Nat
    bar y = {!x!}

-- WAS: Splitting on x produces the following garbage:
-- foo : Nat → Nat
-- foo x = bar x
--   where
--     bar : Nat → Nat
--     bar y = {!!}
--     bar y = {!!}

-- SHOULD: raise an error
