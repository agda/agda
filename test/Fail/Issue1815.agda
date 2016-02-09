-- Regression, introduced by the fix of issue 1759

module Issue1815 where

module _ (A : Set) where

  record R1 : Set where
    field f1 : A

  record R2 : Set where
    field f2 : R1
    open R1 f2 public

-- Parameter A is hidden in type of field f1 in R1 ...
test1 : ∀ A (r : R1 A) → A
test1 A r = R1.f1 r

-- ... and should be so in the type of field f1 in R2, too.
shouldFail : ∀ A (r : R2 A) → A
shouldFail A r = R2.f1 A r
