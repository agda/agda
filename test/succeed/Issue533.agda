module Issue533 where

data Empty : Set where

empty : {A B : Set} → (B → Empty) → B → A
empty f x with f x
... | ()

fail : ∀ {A : Set} → Empty → A
fail {A} = empty absurd
  where
    absurd : _ → Empty
    absurd ()
-- should check (due to postponed emptyness constraint, see issue 479)
