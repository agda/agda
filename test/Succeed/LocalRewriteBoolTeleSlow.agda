{-# OPTIONS --rewriting --no-fast-reduce #-}

open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite

module LocalRewriteBoolTeleSlow where

module Foo (Bool : Set) (tt ff : Bool)
           (elim : (P : Bool → Set) → P tt → P ff → ∀ b → P b)
           (@rew elim-tt : ∀ {P t f} → elim P t f tt ≡ t)
           (@rew elim-ff : ∀ {P t f} → elim P t f ff ≡ f) where
  not : Bool → Bool
  not = elim (λ _ → Bool) ff tt

  not-not : ∀ b → not (not b) ≡ b
  not-not = elim (λ b → not (not b) ≡ b) refl refl

open import Agda.Builtin.Bool

elim : (P : Bool → Set) → P true → P false → ∀ b → P b
elim P t f true  = t
elim P t f false = f

not = Foo.not Bool true false elim refl refl

not-not : ∀ b → not (not b) ≡ b
not-not = Foo.not-not Bool true false elim refl refl
