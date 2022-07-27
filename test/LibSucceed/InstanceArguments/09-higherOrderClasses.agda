{-# OPTIONS --universe-polymorphism #-}

module InstanceArguments.09-higherOrderClasses where

open import Effect.Applicative
open import Effect.Monad
open import Effect.Monad.Indexed
open import Function

lift : ∀ {a b c} {A : Set a} {C : Set c} {B : A → Set b} →
       ({{x : A}} → B x) → (f : C → A) → {{x : C}} → B (f x)
lift m f {{x}} = m {{f x}}

monadToApplicative : ∀ {l} {M : Set l → Set l} → RawMonad M → RawApplicative M
monadToApplicative = RawIMonad.rawIApplicative

liftAToM : ∀ {l} {V : Set l} {M : Set l → Set l} → ({{appM : RawApplicative M}} → M V) →
           {{monadM : RawMonad M}} → M V
liftAToM app {{x}} = lift (λ {{appM}} → app {{appM}}) monadToApplicative {{x}}
