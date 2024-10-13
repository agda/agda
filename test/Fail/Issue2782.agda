-- Andreas, 2024-10-13 duplicating test/Succeed/Issue2782 for --safe

{-# OPTIONS --safe #-}

open import Common.Equality
open import Common.Reflection
open import Common.SafePrelude

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
