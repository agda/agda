------------------------------------------------------------------------
-- The Agda standard library
--
-- A delimited continuation monad
------------------------------------------------------------------------

module Category.Monad.Continuation where

open import Category.Applicative
open import Category.Applicative.Indexed
open import Category.Monad
open import Category.Monad.Identity
open import Category.Monad.Indexed
open import Function
open import Level

------------------------------------------------------------------------
-- Delimited continuation monads

DContT : ∀ {i f} {I : Set i} → (I → Set f) → (Set f → Set f) → IFun I f
DContT K M r₂ r₁ a = (a → M (K r₁)) → M (K r₂)

DCont : ∀ {i f} {I : Set i} → (I → Set f) → IFun I f
DCont K = DContT K Identity

DContTIMonad : ∀ {i f} {I : Set i} (K : I → Set f) {M} →
               RawMonad M → RawIMonad (DContT K M)
DContTIMonad K Mon = record
  { return = λ a k → k a
  ; _>>=_  = λ c f k → c (flip f k)
  }
  where open RawMonad Mon

DContIMonad : ∀ {i f} {I : Set i} (K : I → Set f) → RawIMonad (DCont K)
DContIMonad K = DContTIMonad K IdentityMonad

------------------------------------------------------------------------
-- Delimited continuation operations

record RawIMonadDCont {i f} {I : Set i} (K : I → Set f)
                      (M : IFun I f) : Set (i ⊔ suc f) where
  field
    monad : RawIMonad M
    reset : ∀ {r₁ r₂ r₃} → M r₁ r₂ (K r₂) → M r₃ r₃ (K r₁)
    shift : ∀ {a r₁ r₂ r₃ r₄} →
            ((a → M r₁ r₁ (K r₂)) → M r₃ r₄ (K r₄)) → M r₃ r₂ a

  open RawIMonad monad public

DContTIMonadDCont : ∀ {i f} {I : Set i} (K : I → Set f) {M} →
                    RawMonad M → RawIMonadDCont K (DContT K M)
DContTIMonadDCont K Mon = record
  { monad = DContTIMonad K Mon
  ; reset = λ e k → e return >>= k
  ; shift = λ e k → e (λ a k' → (k a) >>= k') return
  }
  where
  open RawIMonad Mon

DContIMonadDCont : ∀ {i f} {I : Set i}
                   (K : I → Set f) → RawIMonadDCont K (DCont K)
DContIMonadDCont K = DContTIMonadDCont K IdentityMonad
