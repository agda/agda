open import Common.Prelude hiding (_>>=_)
open import Common.Reflection
open import Common.Equality

module Issue2782 where

module Interval where
  private
    data I' : Set where
      Izero' : I'
      Ione'  : I'

  I : Set
  I = I'

  Izero : I
  Izero = Izero'

  Ione : I
  Ione = Ione'

  {--
  postulate
    Iseg : Izero ≡ Ione
  --}

  -- Fails when run with --safe flag in command-line

  unquoteDecl Iseg = declarePostulate (vArg Iseg) (def (quote _≡_) (vArg (def (quote Izero) []) ∷ vArg (def (quote Ione) []) ∷ []))

open Interval public

pf : Izero ≡ Ione
pf = Iseg
