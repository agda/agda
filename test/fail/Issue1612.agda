-- Andreas, 2015-07-21 Issue 1612
-- Error "D is not strictly positive" should appear immediately.
-- (There was a performance problem due to the use of Utils.Graph.....allPaths).

{-# NON_TERMINATING #-}

mutual

  data D : Set where
    c0 : A0 → D
    c1 : A1 → D
    c2 : A2 → D
    c3 : A3 → D
    c4 : A4 → D
    c5 : A5 → D
    c6 : A6 → D
    c7 : A7 → D
    c8 : A8 → D
    c9 : A9 → D

  A0 : Set
  A0 = B0

  B0 : Set
  B0 = A0 → D

  A1 : Set
  A1 = B1

  B1 : Set
  B1 = A1 → D

  A2 : Set
  A2 = B2

  B2 : Set
  B2 = A2 → D

  A3 : Set
  A3 = B3

  B3 : Set
  B3 = A3 → D

  A4 : Set
  A4 = B4

  B4 : Set
  B4 = A4 → D

  A5 : Set
  A5 = B5

  B5 : Set
  B5 = A5 → D

  A6 : Set
  A6 = B6

  B6 : Set
  B6 = A6 → D

  A7 : Set
  A7 = B7

  B7 : Set
  B7 = A7 → D

  A8 : Set
  A8 = B8

  B8 : Set
  B8 = A8 → D

  A9 : Set
  A9 = B9

  B9 : Set
  B9 = A9 → D
