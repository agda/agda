module JSFaceForall where

open import Agda.Builtin.Bool
open import Common.IO renaming (then to _>>_)

-- Exercise the runtime primitive through its Boolean representation.
-- The JavaScript backend currently rejects erased-cubical modules.
postulate faceForall : (Bool → Bool) → Bool
{-# COMPILE JS faceForall = f => agdaRTS.primFaceForall(f) #-}

main : IO _
main = do
  printResult (λ _ → true)
  printResult (λ _ → false)
  printResult (λ b → b)
  printResult (λ { true → false ; false → true })
  where
  printResult : (Bool → Bool) → IO _
  printResult f = printBool (faceForall f) >> putStr "\n"
