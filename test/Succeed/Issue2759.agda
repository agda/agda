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

-- Empty blocks are also tolerated in lets and lambdas.

_ = λ (let abstract ) → let abstract  in Set
_ = λ (let field    ) → let field     in Set
_ = λ (let instance ) → let instance  in Set
_ = λ (let macro    ) → let macro     in Set
_ = λ (let mutual   ) → let mutual    in Set
_ = λ (let postulate) → let postulate in Set
_ = λ (let private  ) → let private   in Set
