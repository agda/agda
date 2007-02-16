
module Nat where

open import Base

data Nat : Set where
  zero : Nat
  suc  : Nat -> Nat

_=N_ : Nat -> Nat -> Set
zero  =N zero  = True
zero  =N suc _ = False
suc _ =N zero  = False
suc n =N suc m = n =N m

refN : Refl _=N_
refN {zero}  = T
refN {suc n} = refN {n}

symN : Sym _=N_
symN {zero}{zero} p   = p
symN {suc n}{suc m} p = symN {n}{m} p
symN {zero}{suc _} ()
symN {suc _}{zero} ()

transN : Trans _=N_
transN {zero }{zero }{zero } p _ = p
transN {suc n}{suc m}{suc l} p q = transN {n}{m}{l} p q
transN {zero }{zero }{suc _} _ ()
transN {zero }{suc _}{_    } () _
transN {suc _}{zero }{_    } () _
transN {suc _}{suc _}{zero } _ ()

