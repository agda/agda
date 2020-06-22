
module _ where

  data Nat : Set where
    zero : Nat
    suc : Nat → Nat
  {-# BUILTIN NATURAL Nat #-}

  _+_ : (m n : Nat) → Nat
  zero + n = n
  suc m + n = suc (m + n)

  data Th : (m n : Nat) → Set where
    os : ∀ {m n} → Th m n → Th (suc m) (suc n)

  Fin : Nat → Set
  Fin = Th (suc zero)

  infixl 6 _++_
  infix 4 _≈M_

  postulate
    U : Set
    RCtx : Nat → Set
    _++_ : ∀ {m n} → RCtx m → RCtx n → RCtx (n + m)
    El : U → RCtx (suc zero)
    _≈M_ : ∀ {n} (Δ0 Δ1 : RCtx n) → Set

  infix 4 _⊢l-var_

  data _⊢l-var_ : ∀ {n} (Δi : RCtx n) (i : Fin n) → Set where
    os : ∀ {n} {e : Th zero n} {Δ Δπ π} (iq : Δπ ≈M (Δ ++ El π)) →
         Δπ ⊢l-var os e

  ⊢l-var-sub : ∀ {n Δ} {i : Fin n} → Δ ⊢l-var i → Set
  ⊢l-var-sub (os iq) = Nat
