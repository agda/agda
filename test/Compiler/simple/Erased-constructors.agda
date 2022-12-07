-- Test case for issue #4638.
-- Partly based on code due to Andrea Vezzosi.

{-# OPTIONS --erasure #-}

open import Common.Prelude

data D : Set where
  run-time        : Bool → D
  @0 compile-time : Bool → D

f : D → @0 D → Bool
f (run-time x)     _                = x
f (compile-time x) (run-time y)     = x
f (compile-time x) (compile-time y) = y

main : IO Unit
main =
  putStrLn (if f (run-time true) (compile-time false)
            then "ok" else "bad")
