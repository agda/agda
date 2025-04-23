module Issue7486 where

postulate
  A : Set

data D : Set where
  con : D

F : D → Set
F con = A

postulate
  instance a : A
  instance i : {d : D} → F d

it : {{A}} → A
it {{x}} = x

-- Failing program because reducible names are now properly considered
-- when they are the head of an instance type. Instance meta goes
-- unsolved with:
--
--    Resolve instance argument _9 : A
--    Candidates
--      a : A
--      i : {d : D} → F d
--      (stuck)
--
-- This is because `i` is tried as an instance for "any class", since
-- the discrimination tree does not record reducts (only that the type
-- is reducible), and at each use site, the conversion checker can
-- invert `F` (it has a proper match and returns a rigid thing, so is
-- injective) to use the `i` instance.
--
-- Pre 2.7.0 was: `i` is an instance for "class `F`", and so is never
-- considered.

x : A
x = it
