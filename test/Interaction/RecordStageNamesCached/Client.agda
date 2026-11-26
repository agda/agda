{-# OPTIONS --double-check #-}
module RecordStageNamesCached.Client where

open import Agda.Builtin.Bool
open import Agda.Builtin.Equality
import RecordStageNamesCached as Source

_ : Source.Public.F false ≡ (Bool → Bool)
_ = refl
