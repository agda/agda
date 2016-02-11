-- Andreas, 2016-02-11. Irrelevant constructors are not (yet?) supported

data D : Set where
  .c : D

-- Should fail, e.g., with parse error.
