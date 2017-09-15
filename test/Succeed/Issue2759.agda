-- Andreas, 2017-09-16, issue #2759
-- Allow empty declaration blocks in the parser.

open import Agda.Builtin.Nat

x0 = zero
mutual
x1 = suc x0
abstract
x2 = suc x1
private
x3 = suc x2
instance
x4 = suc x3
macro
x5 = suc x4
postulate
x6 = suc x5

-- Expected: 6 warnings about empty blocks

mutual
  postulate

-- Empty postulate block.

abstract private instance macro

-- Empty macro block.
