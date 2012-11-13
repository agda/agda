-- Andreas, 2012-11-13 issue reported by joshkos
module Issue754 where

data RDesc (I : Set) : Set₁ where
  ∎  : RDesc I
  ṿ  : (i : I) → RDesc I
  σ  : (S : Set) (D : S → RDesc I) → RDesc I

data ROrn {I J} (e : J → I) : RDesc I → RDesc J → Set₁ where
  ∎ : ROrn e ∎ ∎
  ṿ : ∀ j i → ROrn e (ṿ i) (ṿ j)
  σ : (S : Set) → ∀ {D E} (O : ∀ s → ROrn e (D s) (E s)) → ROrn e (σ S D) (σ S E)
  Δ : (T : Set) → ∀ {D E} (O : ∀ t → ROrn e D (E t)) → ROrn e D (σ T E)

scROrn : ∀ {I J K} {e : J → I} {f : K → J} {D E F} → ROrn e D E → ROrn f E F → ROrn (λ x → e (f x)) D F
scROrn         ∎        ∎        = ∎
scROrn {e = e} ∎        (Δ T P)  = Δ T λ t → scROrn {e = e} ∎ (P t)  -- culprit?
scROrn         (ṿ j i)  (ṿ k .j) = ṿ k i
scROrn {e = e} (ṿ j i)  (Δ T P)  = Δ T λ t → scROrn {e = e} (ṿ j i) (P t)  -- culprit?
scROrn         (σ S O)  (σ .S P) = σ S λ s → scROrn (O s) (P s)
scROrn         (σ S O)  (Δ T P)  = Δ T λ t → scROrn (σ S O) (P t)  -- culprit?
scROrn         (Δ T O)  (σ .T P) = Δ T λ t → scROrn (O t) (P t)
scROrn         (Δ T O)  (Δ T' P) = Δ T' λ t → scROrn (Δ T O) (P t)

-- Internal error message was:
-- blowUpSparseVec (n = 2) aux i=3 j=3 length l = 2

-- The error was triggered by some operations on matrix-shaped orders
-- which did not preserve the internal invariants of sparse matrices.
