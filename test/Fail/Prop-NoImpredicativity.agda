{-# OPTIONS --prop #-}

True : Prop
True = {P : Prop} → P → P

-- Current error (incomprehensible):
-- Set₁ != Set
-- when checking that the expression {P : Prop} → P → P has type Prop
