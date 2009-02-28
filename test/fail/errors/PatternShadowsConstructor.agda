module PatternShadowsConstructor where

module A where

  data B : Set where
    x : B

  data C : Set where
    c : B → C

open A using (C; c)

f : C → C
f (c x) = x
