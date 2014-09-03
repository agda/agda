-- Andreas, 2014-09-02, reported by Nisse

-- {-# OPTIONS -v scope.mod.inst:30 #-}

record R : Set₁ where
  field
    A : Set

-- works : (A : R) → let open R A renaming (A to B) in B → B
-- works _ a = a

test : (A : R) → let open R A in A → A
test _ a = a

-- WAS:
-- Either the A introduced by the let should shadow the outer A, or an
-- ambiguity error should be raised. Current error message:
--
-- R !=< Set of type Set₁
-- when checking that the expression A has type Set

-- NOW: ambiguity error.
