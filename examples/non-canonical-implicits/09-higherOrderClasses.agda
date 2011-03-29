{-# OPTIONS --universe-polymorphism #-}

module 09-higherOrderClasses where

open import Category.Applicative
open import Category.Monad
open import Category.Monad.Indexed
open import Function

lift : ∀ {a b c} {A : Set a} {C : Set c} {B : A → Set b} →
       ({{x : A}} → B x) → (f : C → A) → {{x : C}} → B (f x)
lift m f {{x}} = m {{f x}}

monadToApplicative : ∀ {l} {M : Set l → Set l} → RawMonad M → RawApplicative M
monadToApplicative = RawIMonad.rawIApplicative

liftAToM : ∀ {l} {V : Set l} {M : Set l → Set l} → ({{appM : RawApplicative M}} → M V) → 
           {{monadM : RawMonad M}} → M V
liftAToM app {{x}} = lift (λ {{appM}} → app {{appM}}) monadToApplicative {{x}}
