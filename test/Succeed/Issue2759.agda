-- Andreas, 2017-09-16, issue #2759
-- Allow empty declaration blocks in the parser.
--
-- Andreas, 2024-03-02, issue #6945

--------------------------------------------------------------
-- Empty blocks should be accepted, but trigger a warning.

abstract
data _ where
instance
interleaved mutual
macro
mutual
opaque
opaque unfolding
postulate
primitive
private
variable

--------------------------------------------------------------
-- Empty blocks are also tolerated in lets and lambdas.

_ = λ (let abstract          ) → let abstract           in Set
_ = λ (let data _ where      ) → let data _ where       in Set
_ = λ (let instance          ) → let instance           in Set
_ = λ (let interleaved mutual) → let interleaved mutual in Set
_ = λ (let macro             ) → let macro              in Set
_ = λ (let mutual            ) → let mutual             in Set
_ = λ (let postulate         ) → let postulate          in Set
_ = λ (let primitive         ) → let primitive          in Set
_ = λ (let private           ) → let private            in Set
_ = λ (let variable          ) → let variable           in Set

-- N.B.: Opaque is not allowed in let blocks.
-- _ = λ (let opaque) → let opaque in Set

--------------------------------------------------------------
-- Nesting blocks.

mutual
  postulate

-- Expected: Empty postulate block.

abstract private instance macro

-- Expected:
-- Empty macro block.
-- Useless abstract private instance blocks.
