{-# OPTIONS --exact-split -Werror #-}
open import Agda.Builtin.Bool

not : Bool → Bool
not false = true
not = λ _ → false
