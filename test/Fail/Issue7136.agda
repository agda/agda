-- Andreas, 2024-02-20, issue #7136:
-- Error out on unsupported pattern synonym arguments.

data C : Set where
  c : C → C

pattern p {x = y} = c y
-- Should be rejected: named arguments not supported in pattern synonym lhs.

test : C → C
test (p {x = y}) = y
