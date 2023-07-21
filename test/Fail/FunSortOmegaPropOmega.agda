-- Andreas, 2023-05-17, AIM XXXVI code sprint PropOmega

{-# OPTIONS --prop #-}

open Agda.Primitive

_ : _ → Set → Setω
_ = λ A B → A → B

-- Should not be solved as it can be either Setω or Propω
