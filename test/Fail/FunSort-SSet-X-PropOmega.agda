{-# OPTIONS --prop --two-level #-}

open Agda.Primitive

_ : SSet → _ → Propω
_ = λ A B → A → B

-- Expected error:
-- Propω != funSort SSet _
