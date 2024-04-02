-- Andreas, 2024-03-05, issue #7167
-- Underapplied pattern synonyms with hidden arguments.

data D : Set where
  c : D → {y : D} → D → D

pattern p x {y} z = c x {y} z

f : D → {y : D} → D → D
f = p

-- Error was:
--
-- (z : D) → D !=< D of type Set
-- when checking that the expression λ z → c x {y} z has type D

-- Should succeed.
