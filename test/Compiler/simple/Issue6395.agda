open import Agda.Builtin.IO
open import Agda.Builtin.Nat
open import Agda.Builtin.Unit

postulate x : Nat

{-# FOREIGN GHC
dataCell :: Integer
dataCell = 123456
#-}
{-# COMPILE GHC x = dataCell #-}

postulate printNat : Nat → IO ⊤
{-# COMPILE GHC printNat = print #-}

main = printNat x
