{-# OPTIONS --prop #-}
module Issue8546 where

data Empty : Set where

data Bool : Set where
  false true : Bool

data Squash (A : Set) : Prop where
  squash : A → Squash A

record Unsquash (A : Prop) : Set where
    constructor unsquash
    field resquash : A

escape : Squash Empty → Bool
escape (squash ())

escape-deep : Squash (Unsquash (Squash Empty)) → Bool
escape-deep (squash (unsquash (squash ())))
