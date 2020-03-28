{-# OPTIONS --no-qualified-instances #-}

module NoQualifiedInstances-InAnonymousModule where

postulate
  A : Set
  f : {{A}} → A

module _ where postulate instance a : A

test : A
test = f
