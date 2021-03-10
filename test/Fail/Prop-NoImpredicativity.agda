{-# OPTIONS --prop #-}

True : Prop
True = {P : Prop} → P → P

-- Old error (incomprehensible):
-- Set₁ != Set
-- when checking that the expression {P : Prop} → P → P has type Prop

-- New error:
-- Prop₁ != Prop
-- when checking that the expression {P : Prop} → P → P has type Prop
