-- Andreas, 2023-09-27, regression test for issue #1702

data D : Set where
  private
    c : D

-- Agda does not allow `private` inside `data` and should complain here.
