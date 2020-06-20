-- Not using any Floats so shouldn't need ieee754 installed.
-- .flags file contains
--    -c --ghc-flag="-hide-package ieee754"

module _ where

open import Agda.Builtin.IO
open import Agda.Builtin.Unit

postulate
  return : {A : Set} → A → IO A

{-# COMPILE GHC return = \ _ -> return #-}

main : IO ⊤
main = return _
