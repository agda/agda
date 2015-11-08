
open import Common.Prelude
open import Common.Reflection

postulate
  X Y : Set

isX : QName → Bool
isX (quote X) = true
isX _ = false


main : IO Unit
main = putStrLn ((if isX (quote X) then "yes" else "no") +S+
                 (if isX (quote Y) then "yes" else "no"))
