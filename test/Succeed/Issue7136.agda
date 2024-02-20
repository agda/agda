-- Andreas, 2024-02-20, issue #7136:
-- Error out on unsupported pattern synonym arguments.

data C : Set where
  c : C → C

-- This special case of named arguments in pattern lhss sneaked in by accident
-- into Agda 2.6.0, so we continue to support it.

pattern p {x = x} = c x

test : C → C
test (p {x = y}) = y

-- Should be accepted
