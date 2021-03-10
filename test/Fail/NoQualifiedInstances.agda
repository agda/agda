{-# OPTIONS --no-qualified-instances #-}

postulate
  A : Set
  f : {{A}} → A

module M where postulate instance a : A

test : A
test = f
