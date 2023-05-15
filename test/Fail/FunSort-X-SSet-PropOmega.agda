{-# OPTIONS --prop --two-level #-}

open Agda.Primitive

_ : _ → SSet → Propω
_ = λ A B → A → B

-- Expected error:
-- Propω != funSort _ SSet
