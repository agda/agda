
module _ (C Dummy : Set) where

data Maybe : Set where
  nothing : Maybe

IfJust : Maybe → Set → Set
IfJust nothing P = P

postulate
  qCtx     : C
  inferRes : Maybe

                             -- v-- Implicit is important here
inferResBest : IfJust inferRes ({G : Maybe} → C)
inferResBest with inferRes
inferResBest | nothing = qCtx    -- Error: Dummy != C when checking qCtx : C

-- Test also with an existing implicit argument
inferResBest₁ : {A : Set} → IfJust inferRes ({G : Maybe} → C)
inferResBest₁ with inferRes
inferResBest₁ | nothing = qCtx    -- Error: Dummy != C when checking qCtx : C

-- Make sure it does break down on underapplied clauses
underapplied : Maybe → C
underapplied with inferRes
underapplied | nothing = λ _ → qCtx
