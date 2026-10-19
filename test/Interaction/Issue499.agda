
module Issue499 where

data A : Set where
  a : A

data B : Set where
  b : .A → B

data C : B → Set where
  c : C (b a)

f : ∀ {i} → C i → A
f x = {!!} -- Hitting C-c C-c x
