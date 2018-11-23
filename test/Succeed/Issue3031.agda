
module _ where

open import Agda.Builtin.Nat hiding (_+_)
import Agda.Builtin.Nat as N
open import Agda.Builtin.TrustMe
open import Agda.Builtin.Equality
open import Agda.Builtin.Sigma

data ⊥ : Set where

module SimplifiedTestCase where

  record Fin : Set where
    constructor mkFin
    field m .p : Nat

  module _ (m : Nat) .(k : Nat) where

    w : Fin
    w = mkFin m k

    mutual

      X : Fin
      X = _

      -- Worked if removing this
      constr₁ : Fin.m X ≡ m
      constr₁ = refl

      constr₂ : X ≡ w
      constr₂ = refl

module OriginalTestCase where

  record Fin (n : Nat) : Set where
    constructor mkFin
    field
      m : Nat
      .p : Σ Nat λ k → (Nat.suc k N.+ m) ≡ n


  apply2 : {t₁ : Set} {t₂ : Set} {a b : t₁} → (f : t₁ → t₂) → a ≡ b → f a ≡ f b
  apply2 f refl = refl

  private
    resurrect : .⊥ → ⊥
    resurrect ()

    refute : ∀ m → (Σ Nat λ x → (suc (x N.+ m) ≡ 0)) → ⊥
    refute m (_ , ())

    lem : ∀ m → .(Σ Nat λ x → (suc (x N.+ m) ≡ 0)) → ⊥
    lem m p = resurrect (refute m p)

  S : ∀ {n} → Fin n → Fin (suc n)
  S (mkFin a kp) = mkFin (suc a) (suc (fst kp) , primTrustMe)

  to : ∀ {n} → Fin n → Fin n
  to record { m = zero ; p = p } = record { m = zero ; p = p }
  to {zero} record { m = (suc m) ; p = p } with lem (suc m) p
  ... | ()
  to {suc n} record { m = (suc m) ; p = p } = S (to record { m = m ; p = fst p , primTrustMe })

  from = to

  iso : ∀ {n} → (x : Fin n) → from (to x) ≡ x
  iso {zero} record { m = m ; p = p } with lem m p
  ... | ()
  iso {suc n} record { m = zero ; p = p } = refl
  iso {suc n} record { m = (suc m) ; p = p } =
    let
      w : Fin n
      w = mkFin m (fst p , primTrustMe)
      v : S (from (to w)) ≡ S w
      v = apply2 {b = _} S (iso w)
    in v
