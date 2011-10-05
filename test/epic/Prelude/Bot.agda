module Prelude.Bot where

data Bot : Set where

magic : ∀{A : Set} -> Bot -> A
magic ()