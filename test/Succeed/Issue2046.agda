-- Andreas, 2016-12-12, issue #2046, reported by Nad
-- Parameter refinement broke the size solver.

-- {-# OPTIONS -v tc.size.solve:100 #-}
-- {-# OPTIONS -v tc.constr.cast:100 #-}
-- -- {-# OPTIONS -v tc.sig.param:60 #-}
-- -- {-# OPTIONS -v tc.check.internal:100 #-}
-- -- {-# OPTIONS -v interaction.give:100 #-}

{-# OPTIONS --sized-types #-}

open import Agda.Builtin.Size using (Size; Size<_)

data _×_ (A B : Set) : Set where
  _,_ : A → B → A × B

record Always {A : Set} (P : A → Set) : Set where
  field
    always : ∀ x → P x

postulate
  A : Set

module M (P : A → Set) where

  record R₁ (i : Size) (x : A) : Set where
    coinductive
    field
      force : {j : Size< i} → R₁ j x

  record R₂ (i : Size) (x : A) : Set where
    inductive
    constructor ⟨_,_⟩
    field
      f₁ : P x
      f₂ : P x → R₁ i x

data P : A → Set where
  c : (y : A) → P y → P y

postulate
  p : (x : A) → P x
  a : (i : Size) → Always (M.R₁ P i)

module _ (Unused : Set) where

  open M P

  rejected : ∀ i z → R₂ i z
  rejected i z =
    ⟨ p z
    , (λ { (c y q) →  Always.always (a _) z   })
    ⟩

-- Should succeed

{-
Solving constraints (DontDefaultToInfty)
i =< _i_31 Unused i z : Size
_i_31 Unused i z =< _i_35 z Unused i q : Size
converting size constraint i =< _i_31 Unused i z : Size
converting size constraint
_i_31 Unused i z =< _i_35 z Unused i q : Size
Solving constraint cluster
[Unused, i, z] i ≤ _i_31 Unused i z
[z, Unused, i, q] _i_31 Unused i z ≤ _i_35 z Unused i q
Size hypotheses
Canonicalized constraints
[z, Unused, i, q] Unused ≤ _i_31 z Unused i
[z, Unused, i, q] _i_31 Unused i z ≤ _i_35 z Unused i q
solution  _i_31 z Unused i  :=  Unused
  xs = [3,2,1]
  u  = Var 2 []
solution  _i_35 z Unused i q  :=  Unused
  xs = [3,2,1,0]
  u  = Var 2 []
-}
