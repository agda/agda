-- Andreas, 2023-05-17, issue #6648

{-# OPTIONS --level-universe #-}

open Agda.Primitive

_ : _ → Set → Setω
_ = λ A B → A → B

-- Should not be solved as it can be either Setω or LevelUniv
