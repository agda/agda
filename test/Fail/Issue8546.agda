{-# OPTIONS --prop #-}
module Issue8546 where

data Empty : Set where

data Bool : Set where
    false true : Bool

data Squash (A : Set) : Prop where
    squash : A → Squash A

data Payload : Bool → Set where
  payload : Bool → Payload true

bad-escape : ∀ (b : Bool) → Squash (Payload b) → Bool
bad-escape false (squash ())
bad-escape true (squash (payload x)) = x
