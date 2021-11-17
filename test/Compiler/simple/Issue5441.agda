open import Agda.Builtin.IO using (IO)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Unit using (⊤)

data D : Set where
  c₁ c₂ : D

f : D → Set → String
f c₁ = λ _ → "OK"
f c₂ = λ _ → "OK"

-- The following pragma should refer to the generated Haskell name
-- for f.

{-# FOREIGN GHC {-# NOINLINE d_f_8 #-} #-}

x : String
x = f c₁ ⊤

postulate
  putStrLn : String → IO ⊤

{-# FOREIGN GHC import qualified Data.Text.IO #-}
{-# COMPILE GHC putStrLn = Data.Text.IO.putStrLn #-}

main : IO ⊤
main = putStrLn x
