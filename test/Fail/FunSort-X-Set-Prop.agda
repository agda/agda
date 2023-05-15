{-# OPTIONS --prop #-}

open Agda.Primitive

_ : _ → Prop → Set
_ = λ A B → A → B

-- Expected error:
-- Setω != funSort _ Prop
