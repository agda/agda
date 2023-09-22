{-# OPTIONS --two-level #-}

open Agda.Primitive

_ : _ → SSet → Setω
_ = λ A B → A → B

-- Expected error:
-- Setω != funSort _ SSet
