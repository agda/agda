-- Andreas, 2017-10-17, issue #2807
--
-- Refining with an extended lambda gave internal error.
-- Seemed to be triggered only when giving resulted in an error.

{-# OPTIONS --allow-unsolved-metas #-}

-- {-# OPTIONS -v scope.extendedLambda:60 #-}
-- {-# OPTIONS -v impossible:10 #-}

data ⊥ : Set where
  actuallyNotEmpty : ⊥

data D : Set where
  c : ⊥ → D

test : D → ⊥
test = {! λ{ (c ()) }!}  -- C-c C-r

-- WAS: internal error in ConcreteToAbstract (insertApp)
--
-- Expected:
-- Succeed with unsolved constraints and metas.
