-- Andreas, 2015-07-07 continuation of issue 665

{-# OPTIONS --show-implicit #-}
-- {-# OPTIONS -v tc.with.strip:60 -v tc.lhs:10 #-}

postulate
  C : Set
  anything : C

record I : Set where
  constructor c
  field
    f : C

data Wrap : (j : I) → Set where
  wrap : ∀ {j} → Wrap j

works1 : ∀ {j} → Wrap j → C
works1 {c _} (wrap {c x}) with anything
... | z = z

works2 : ∀ {j} → Wrap j → C
works2 (wrap {_}) with anything
... | z = z

works3 : ∀ {j} → Wrap j → C
works3 wrap with anything
... | z = z

works : ∀ {j} → Wrap j → C
works {c _} (wrap {c _}) with anything
works {c _} (wrap .{c _}) | z = z

test : ∀ {j} → Wrap j → C
test {c _} (wrap {c _}) with anything
test {c _} (wrap {c _}) | z = z

test' : ∀ {j} → Wrap j → C
test' {c _} (wrap {c _}) with anything
... | z = z

-- ERROR WAS::
-- Inaccessible (dotted) patterns from the parent clause must also be
-- inaccessible in the with clause, when checking the pattern {c ._},
-- when checking that the clause
-- test {c _} (wrap {c ._}) with anything
-- test {c _} (wrap {c ._}) | z = z
-- has type {j : I} → Wrap j → C

works1a : ∀ {j} → Wrap j → C
works1a {c _} (wrap {c x}) with anything
works1a {c _} (wrap {c x}) | z = z

works1b : ∀ {j} → Wrap j → C
works1b .{c _} (wrap {c x}) with anything
works1b .{c _} (wrap {c x}) | z = z

-- ERROR WAS:
-- With clause pattern .(c _) is not an instance of its parent pattern
-- (c .(Var 0 []) : {I})
-- when checking that the clause
-- works1b {c ._} (wrap {c _}) with anything
-- works1b {.(c _)} (wrap {c _}) | z = z
-- has type {j : I} → Wrap j → C

-- should pass
