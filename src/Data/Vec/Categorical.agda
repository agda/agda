------------------------------------------------------------------------
-- The Agda standard library
--
-- A categorical view of Vec
------------------------------------------------------------------------

module Data.Vec.Categorical {a n} where

open import Category.Applicative using (RawApplicative)
open import Category.Applicative.Indexed using (Morphism)
open import Category.Functor as Fun using (RawFunctor)
open import Category.Functor.Identity using (IdentityFunctor)
open import Category.Monad using (RawMonad)
open import Category.Monad.Identity using (IdentityMonad)
open import Data.Fin using (Fin)
open import Data.Vec
open import Data.Vec.Properties

functor : RawFunctor (λ (A : Set a) → Vec A n)
functor = record
  { _<$>_ = map
  }

applicative : RawApplicative (λ (A : Set a) → Vec A n)
applicative = record
  { pure = replicate
  ; _⊛_  = _⊛_
  }

-- lookup is a functor morphism from Vec to Identity.

lookup-functor-morphism : (i : Fin n) →
                          Fun.Morphism functor IdentityFunctor
lookup-functor-morphism i = record
  { op     = lookup i
  ; op-<$> = lookup-map i
  }

-- lookup is an applicative functor morphism.

lookup-morphism : (i : Fin n) →
                  Morphism applicative (RawMonad.rawIApplicative IdentityMonad)
lookup-morphism i = record
  { op      = lookup i
  ; op-pure = lookup-replicate i
  ; op-⊛    = lookup-⊛ i
  }
