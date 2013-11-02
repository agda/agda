-- {-# OPTIONS -v tc.lhs.shadow:30 #-}

module PatternShadowsConstructor3 where

data Bool : Set where
  true false : Bool

module A where

  data B : Set where
    x : B

  data C : Set where
    c : B → C

open A using (C; c)

T : Bool → Set
T true = C → C
T false = Bool

f : (b : Bool) → T b
f true (c x) = x
f false = true
