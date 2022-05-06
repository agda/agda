-- AIM XXXV, 2022-05-06, issue #5891.
-- When checking that the sort of a data type admits data definitions
-- (checkDataSort), we need to handle the case of PiSort.

mutual
  Univ1 = _
  Univ2 = _
  Univ3 = _

  postulate
    A1 : Univ1
    A2 : Univ2

  A : Univ3
  A = A1 → A2

  -- This demonstrates that the sort of a data types can be a PiSort
  -- (temporarily, until further information becomes available later):
  data Empty : Univ3 where

  _ : Univ1
  _ = Set

  _ : Univ2
  _ = Set

-- Should succeed.
