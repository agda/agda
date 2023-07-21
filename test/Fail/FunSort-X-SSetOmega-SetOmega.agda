{-# OPTIONS --two-level #-}

open Agda.Primitive

_ : _ → SSetω → Setω
_ = λ A B → A → B

-- Expected error:
-- Setω != funSort _ SSetω
