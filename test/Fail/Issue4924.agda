module Issue4924 where

record R (T : Set) : Set where
  field
    f : T → T

module _ {A B : Set} (ra : R A) (rb : R B) (pri : {T : Set} → {{r : R T}} → T) where
  open R ra
  open R rb

  instance
    _ = ra

  _ : A
  _ = f pri
