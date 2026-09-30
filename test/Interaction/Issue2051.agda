-- Andreas, 2016-06-20 issue #2051
-- Try to preserve rhs when splitting a clause

data D : Set where
  d : D
  c : D → D

-- A simple RHS that should be preserved by splitting:

con : (x : D) → D
con x = c {!x!}  -- C-c C-c

-- More delicate, a meta variable applied to something:
-- This means the hole is not at the rightmost position.

app : (x : D) → D
app x = {!x!} x

-- A let-binding (not represented in internal syntax):

test : (x : D) → D
test x = let y = c in {!x!}  -- C-c C-c

-- Case splitting replaces entire RHS by hole
--   test c = ?
