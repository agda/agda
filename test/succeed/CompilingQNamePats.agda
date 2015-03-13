
open import Common.Prelude
open import Common.Reflection

postulate
  X Y : Set

isX : QName → Bool
isX (quote X) = true
isX _ = false

postulate
  putStrLn : String → IO Unit

{-# COMPILED putStrLn putStrLn #-}

primitive primStringAppend : String → String → String

infixr 5 _&_
_&_ = primStringAppend

main : IO Unit
main = putStrLn ((if isX (quote X) then "yes" else "no") &
                 (if isX (quote Y) then "yes" else "no"))
