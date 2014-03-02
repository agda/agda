-- Andreas, 2014-03-02, issue and test case by Nisse

-- {-# OPTIONS --show-implicit -v tc.meta.assign:25 -v tc.meta.occurs:70 -v tc.meta.kill:30 #-}
-- {-# OPTIONS -v tc:10 #-}

record Σ (A : Set) (B : A → Set) : Set where
  constructor _,_
  field
    proj₁ : A
    proj₂ : B proj₁

open Σ public

postulate
  A : Set
  D : A → Set

data P : ∀ {xP} → D xP → Set where
  c : ∀ {xc} (dc : D xc) → P dc

module M (f : ∀ {x} → D x → Σ A D)
         (_ : ∀ {xM} (dM : D xM) → P (proj₂ (f dM)))
  where

  postulate
    p : ∀ {x} → D x → A
    q : ∀ {x} {d : D x} → D (p d)

p : ∀ {x} → D x → A
p = M.p (λ x → _ , x) c

q : ∀ {xq} {dq : D xq} → D (p dq)
q = M.q _ c

-- WAS: Unsound pruning of metas under projections
--
-- Cannot instantiate the metavariable _49 to solution d since it
-- contains the variable d which is not in scope of the metavariable
-- or irrelevant in the metavariable but relevant in the solution
-- when checking that the expression c has type ((d : D .x₁) → P _49)

-- NOW: type-checks fine
