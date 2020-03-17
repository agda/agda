{-# OPTIONS --no-qualified-instances #-}

module NoQualifiedInstances-AnonymousInstance where

postulate
  A : Set
  f : {{A}} → A

postulate instance _ : A

test : A
test = f
