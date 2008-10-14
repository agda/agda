------------------------------------------------------------------------
-- A Delimited Continuation Monad
------------------------------------------------------------------------

module Category.Monad.Continuation where

open import Category.Applicative
open import Category.Applicative.Indexed
open import Category.Monad
open import Category.Monad.Indexed
open import Category.Monad.Identity

open import Data.Function

------------------------------------------------------------------------
-- Delimited Continuation Monads

DContT : {I : Set} -> (I -> Set) -> (Set -> Set) -> IFun I
DContT K M r₂ r₁ a = (a -> M (K r₁)) -> M (K r₂)

DCont : {I : Set} -> (I -> Set) -> IFun I
DCont K = DContT K Identity

DContTIMonad : forall {I}(K : I -> Set) {M} ->
               RawMonad M -> RawIMonad (DContT K M)
DContTIMonad K Mon = record
  { return = \a k -> k a
  ; _>>=_ = \c f k -> c (flip f k)
  }
  where open RawMonad Mon

DContIMonad : forall {I}(K : I -> Set) -> RawIMonad (DCont K)
DContIMonad K = DContTIMonad K IdentityMonad

------------------------------------------------------------------------
-- Delimited Continuation Operations

record RawIMonadDCont {I : Set} (K : I -> Set)
                      (M : I -> I -> Set -> Set) : Set1 where
  field
    monad : RawIMonad M
    reset : forall {r₁ r₂ r₃} -> M r₁ r₂ (K r₂) -> M r₃ r₃ (K r₁)
    shift : forall {a r₁ r₂ r₃ r₄} -> ((a -> M r₁ r₁ (K r₂)) -> M r₃ r₄ (K r₄)) -> M r₃ r₂ a

  open RawIMonad monad public

DContTIMonadDCont : forall {I} (K : I -> Set) {M} ->
                    RawMonad M -> RawIMonadDCont K (DContT K M)
DContTIMonadDCont K Mon = record
  { monad = DContTIMonad K Mon
  ; reset = \e k -> e return >>= k
  ; shift = \e k -> e (\a k' -> (k a) >>= k') return
  }
  where
  open RawIMonad Mon

DContIMonadDCont : forall {I} (K : I -> Set) -> RawIMonadDCont K (DCont K)
DContIMonadDCont K = DContTIMonadDCont K IdentityMonad
