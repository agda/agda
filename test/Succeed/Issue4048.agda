{-# OPTIONS --rewriting #-}
module Issue4048 where

data _==_ {i} {A : Set i} : (x y : A) → Set i where
  refl : {a : A} → a == a
{-# BUILTIN REWRITE _==_ #-}

postulate
  Π : (A : Set) (B : A → Set) → Set
  lam : {A : Set} {B : A → Set} (b : (a : A) → B a) → Π A B
  app : {A : Set} {B : A → Set} (f : Π A B) (a : A) → B a
  Π-β : {A : Set} {B : A → Set} (b : (a : A) → B a) (a : A) → app (lam b) a == b a
  {-# REWRITE Π-β #-}

postulate
  ⊤ : Set
  tt : ⊤
  ⊤-elim : ∀ {i} (A : ⊤ → Set i) (d : A tt) (x : ⊤) → A x
  ⊤-β : ∀ {i} (A : ⊤ → Set i) (d : A tt) → ⊤-elim A d tt == d
  {-# REWRITE ⊤-β #-}

tt' : ⊤
tt' = tt

module _
  (C : (p : ⊤) → Set)
  (z : C tt)
  where

  F : (n p x : ⊤) → C p
  F n p = app (⊤-elim (λ n → (p : ⊤) → Π ⊤ (λ _ → C p))
                       (⊤-elim _ (lam (⊤-elim _ z)))
                       n p)

  F-red : F tt tt tt == z
  F-red = refl

  -- Bug?
  F-red' : F tt tt' tt == z
  F-red' = refl  -- Not accepted, even though tt' is tt by definition.
