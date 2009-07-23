module PatternShadowsConstructor2 where

module A where

  data A (X : Set) : Set where
    c : A X → A X
    x : A X

open A using (A; c)

f : ∀ {X} → A X → A X → A X
f (c y) x = x
f A.x   _ = A.x
