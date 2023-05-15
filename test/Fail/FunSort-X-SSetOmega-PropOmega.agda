{-# OPTIONS --prop --two-level #-}

open Agda.Primitive

_ : _ → SSetω → Propω
_ = λ A B → A → B

-- Expected error:
-- Propω != funSort _ SSetω
