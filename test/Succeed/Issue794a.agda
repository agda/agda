module Issue794a where

open import Common.Prelude
open import Common.MAlonzo

postulate A : Set

id : .A → A → A
id x y = y
