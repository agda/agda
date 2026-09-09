{-# OPTIONS --prop #-}
module Issue8546 where

data Empty : Set where

data _≡_ {A : Set} (a : A) : A -> Set where
    refl : a ≡ a

data Bool : Set where
  false true : Bool

data Squash (A : Set) : Prop where
  squash : A → Squash A

record Unsquash (A : Prop) : Set where
    constructor unsquash
    field resquash : A

escape-empty : Squash Empty → Bool
escape-empty (squash ())

escape-eq : ∀ {b1 b2 : Bool} -> Squash (b1 ≡ b2) -> b1 ≡ b2
escape-eq {false} {false} _ = refl
escape-eq {false} {true} (squash ())
escape-eq {true} {false} (squash ())
escape-eq {true} {true} _ = refl

escape-deep : Squash (Unsquash (Squash Empty)) → Bool
escape-deep (squash (unsquash (squash ())))
