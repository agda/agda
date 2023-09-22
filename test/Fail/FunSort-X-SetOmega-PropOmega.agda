{-# OPTIONS --prop #-}

open Agda.Primitive

_ : _ → Setω → Propω
_ = λ A B → A → B

-- Expected error:
-- Propω != funSort _ Setω
