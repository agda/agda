open import Agda.Builtin.IO
open import Agda.Builtin.Size
open import Agda.Builtin.Unit

data D (i : Size) : Set where

{-# FOREIGN GHC
  data Empty i
  #-}

{-# COMPILE GHC D = data Empty () #-}

f : ∀ {i} → D i → D i
f ()

{-# COMPILE GHC f as f #-}

postulate
  return : {A : Set} → A → IO A

{-# COMPILE GHC return = \_ -> return #-}

main : IO ⊤
main = return _
