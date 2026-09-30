module Issue2487-4 where

open import Agda.Primitive -- this should not be consistency-checked

open import Agda.Builtin.Bool

f : Bool → Bool
f true = true
f _    = false
