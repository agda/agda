-- Andreas, 2016-09-12
--
-- Underscores should also get meaningful names
-- (not just metas from omitted hidden arguments)

-- {-# OPTIONS -v tc.meta.name:100 #-}

postulate
  F : (A : Set) → Set
  G : {B : Set} → Set

test1 : Set
test1 = F _
  -- name of this meta should be _A_0

test2 : Set
test2 = G
  -- creates meta _B_1

test3 : Set
test3 = G {_}
  -- name of this meta should be _B_2
