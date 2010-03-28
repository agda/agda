module Issue252 where

data I : Set where
  zero : I

data D : I → Set where
  c : ∀ i → D i → D i

id : I → I
id i = i

index : ∀ i → D i → I
index i _ = i

foo : ∀ i → D i → D zero
foo .i (c i d) with id i
foo .i (c i d) | zero = d

bar : ∀ i → D i → D zero
bar .i (c i d) with index i d
bar .i (c i d) | zero = d

-- In the context of the first goal d has type D i′, in the second it
-- has type D i. Well, not any more.
