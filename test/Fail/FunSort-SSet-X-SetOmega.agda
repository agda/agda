{-# OPTIONS --two-level #-}

open Agda.Primitive

_ : SSet → _ → Setω
_ = λ A B → A → B

-- Expected error:
-- Setω != funSort SSet _
