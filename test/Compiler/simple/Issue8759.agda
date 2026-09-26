open import Agda.Builtin.Bool
open import Agda.Builtin.IO
open import Agda.Builtin.String
open import Agda.Builtin.Unit

postulate
  putStrLn : String → IO ⊤

{-# FOREIGN GHC import qualified Data.Text.IO #-}
{-# COMPILE GHC putStrLn = Data.Text.IO.putStrLn #-}
{-# COMPILE JS putStrLn = x => k => k(console.log(x)) #-}

data D : Set where
  c : D
  d : Bool → D → D

f : D → String
f c                    = "A"
f (d true c)           = "B"
f (d false c)          = "C"
f (d true (d true _))  = "D"
f (d false (d true _)) = "E"
f (d _ (d false _))    = "F"

main : IO ⊤
main = putStrLn (f (d false c))
