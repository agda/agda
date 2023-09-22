-- Andreas, 2018-08-14, re issue #1556
-- Termination checking functions over inductive-inductive types

{-# OPTIONS --forced-argument-recursion #-}
-- {-# OPTIONS -v term:40 #-}

mutual
  data Cxt : Set where
    ε    :  Cxt
    _,_  :  (Γ : Cxt) (A : Ty Γ) → Cxt

  data Ty : (Γ : Cxt) → Set where
    u  :  ∀ Γ → Ty Γ
    Π  :  ∀ Γ (A : Ty Γ) (B : Ty (Γ , A)) → Ty Γ

mutual
  f : Cxt → Cxt
  f ε        =  ε
  f (Γ , T)  =  (f Γ , g Γ T)

  g : ∀ Γ → Ty Γ → Ty (f Γ)
  g Γ (u .Γ)      =  u (f Γ)
  g Γ (Π .Γ A B)  =  Π (f Γ) (g Γ A) (g (Γ , A) B)

-- The type of g contains a call
--
--   g Γ _ --> f Γ
--
-- which is now recorded by the termination checker.

-- Should pass termination.
