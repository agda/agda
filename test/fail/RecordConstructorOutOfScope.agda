module RecordConstructorOutOfScope where

record R : Set where
  constructor con

  id : R
  id = con
