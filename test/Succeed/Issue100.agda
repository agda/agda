
module Issue100 where

-- hiding (Nat) goes on the 'open' not on the 'import'.
open import Nat hiding (Nat)

one : Nat.Nat
one = suc zero
