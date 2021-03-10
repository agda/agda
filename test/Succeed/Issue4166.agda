
open import Agda.Builtin.Bool

open import Issue4166.Import {b = true} as A′

it : ⦃ Bool ⦄ → Bool
it ⦃ b ⦄ = b

b : Bool
b = it
