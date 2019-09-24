{-# OPTIONS --prop #-}

postulate
  f : Prop → Prop
  P : Prop₁

x : Prop
x = f P

-- WAS:
-- Set₁ != Set
-- when checking that the expression P has type Prop

-- SHOULD BE:
-- Prop₁ != Prop
-- when checking that the expression P has type Prop
