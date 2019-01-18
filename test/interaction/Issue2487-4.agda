module Issue2487-4 where

open import Agda.Builtin.Bool

f : Bool → Bool
f true = true
f _    = false
