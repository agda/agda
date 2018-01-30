open import Agda.Builtin.IO
open import Agda.Builtin.Nat
open import Agda.Builtin.Size
open import Agda.Builtin.Unit

mutual

  data Delay (A : Set) (i : Size) : Set where
    now   : A → Delay A i
    later : Delay′ A i → Delay A i

  record Delay′ (A : Set) (i : Size) : Set where
    coinductive
    field
      force : {j : Size< i} → Delay A j

open Delay′ public

delay : ∀ {A i} → Nat → A → Delay A i
delay zero    x = now x
delay (suc n) x = later λ { .force → delay n x }

data Maybe (A : Set) : Set where
  nothing : Maybe A
  just    : A → Maybe A

{-# COMPILE GHC Maybe = data Maybe (Nothing | Just) #-}

run : ∀ {A} → Nat → Delay A ∞ → Maybe A
run zero    _         = nothing
run (suc n) (now x)   = just x
run (suc n) (later x) = run n (force x)

postulate
  wrapper : Maybe Nat → IO ⊤

{-# COMPILE GHC wrapper = print #-}

main : IO ⊤
main = wrapper (run 10 (delay 5 12))
