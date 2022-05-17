{-# OPTIONS --without-K --safe --no-sized-types --no-guardedness #-}

module Agda.Builtin.Reflection.External where

open import Agda.Builtin.List
open import Agda.Builtin.Nat
open import Agda.Builtin.Sigma
open import Agda.Builtin.String
open import Agda.Builtin.Reflection

postulate
  execTC : String → List String → String
         → TC (Σ Nat (λ _ → Σ String (λ _ → String)))

{-# BUILTIN AGDATCMEXEC execTC #-}

{-# COMPILE JS execTC = _ => _ => _ => undefined #-}
