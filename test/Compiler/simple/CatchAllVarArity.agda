-- Mixing CatchAll branches with varying arity can be tricky.
--
-- If the number of arguments a catch all branch expects to be already abstracted over is smaller
-- than the number of arguments present in the failing clause/branch, we need to apply
-- the catch-all branch to the surplus arguments already abstracted over.

module CatchAllVarArity where

open import Common.Nat
open import Common.IO
open import Common.Unit


f : Nat → Nat → Nat
f zero = λ y → y
f (suc zero) (suc y) = suc y
f x y = (suc y)

case_of_ : ∀{A B : Set} → A → (A → B) → B
case a of f = f a

-- case tree variant of f
g : Nat → Nat → Nat
g = λ x →
    case x of
     λ{ zero     → λ y → y
      ; (suc x') →
        case x' of
         λ{ zero  → λ y →
            case y of
             λ{ (suc y') → suc y'
              ; _        → fallback (suc x') y
              }
          ; _ → λ y → fallback x y
          }
      }
  where
    fallback = λ x y → suc y

--expected:
-- 10
-- 21
-- 1
-- 0
-- 4
-- 1
main = printNat (f 0 10) ,,
  putStrLn "" ,,
  printNat (f 10 20) ,,
  putStrLn "" ,,
  printNat (f 10 0) ,,
  putStrLn "" ,,
  printNat (f 0 0) ,,
  putStrLn "" ,,
  printNat (f 1 4) ,,
  putStrLn "" ,,
  printNat (f 1 0) ,,
  putStrLn ""
