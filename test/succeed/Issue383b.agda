-- Andreas, 2011-05-09
-- {-# OPTIONS -v tc.inj:40 -v tc.meta:30 #-}
module Issue383b where

postulate
  Σ  : (A : Set) → (A → Set) → Set
  U  : Set
  El : U → Set

mutual

  data Ctxt : Set where
    _▻_ : (Γ : Ctxt) → (Env Γ → U) → Ctxt

  Env : Ctxt → Set
  Env (Γ ▻ σ) = Σ (Env Γ) λ γ → El (σ γ)

postulate
  Δ : Ctxt
  σ : Env Δ → U
  δ : U → Env (Δ ▻ σ)

data Foo : (Γ : Ctxt) → (U → Env Γ) → Set where
  foo : Foo _ δ

-- WORKS NOW;  OLD COMPLAINT:
-- Agda does not solve or simplify the following constraint. Why? Env
-- is constructor-headed.
--
-- _40 := δ  if  [(Σ (Env Δ) (λ γ → El (σ γ))) =< (Env _39) : Set]
