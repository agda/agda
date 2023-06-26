-- Andreas, 2019-06-26, issue #3855
-- Mark erased hypotheses as such in a non-erased goal.
-- Same for irrelevance.

-- Andreas, 2023-06-26, issue #6706.
-- Shape-irrelevant hypotheses should be printed as such.

{-# OPTIONS --erasure #-}

Goal :
  (        A : Set)
  (@0      B : Set)
  (@irr    C : Set)
  (@0 @irr D : Set)
  (@shirr  E : Set)
  (        A : Set)
  (@0      B : Set)
  (@irr    C : Set)
  (@0 @irr D : Set)
  (@shirr  E : Set)
  → Set
Goal A B C D E = λ A B C D E → {!!}

-- Goal: Set
-- ————————————————————————————————————————————————————————————
-- E      : Set   (shape-irrelevant)
-- D      : Set   (erased, irrelevant)
-- C      : Set   (irrelevant)
-- B      : Set   (erased)
-- A      : Set
-- E = E₁ : Set   (not in scope, shape-irrelevant)
-- D = D₁ : Set   (not in scope, erased, irrelevant)
-- C = C₁ : Set   (not in scope, irrelevant)
-- B = B₁ : Set   (not in scope, erased)
-- A = A₁ : Set   (not in scope)


-- Don't show erasure in erased goal!

@0 ErasedGoal :
  (        A : Set)
  (@0      B : Set)
  (@irr    C : Set)
  (@0 @irr D : Set)
  (@shirr  E : Set)
  (        A : Set)
  (@0      B : Set)
  (@irr    C : Set)
  (@0 @irr D : Set)
  (@shirr  E : Set)
  → Set
ErasedGoal A B C D E = λ A B C D E → {!!}

-- Goal: Set
-- ————————————————————————————————————————————————————————————
-- E      : Set   (shape-irrelevant)
-- D      : Set   (irrelevant)
-- C      : Set   (irrelevant)
-- B      : Set
-- A      : Set
-- E = E₁ : Set   (not in scope, shape-irrelevant)
-- D = D₁ : Set   (not in scope, irrelevant)
-- C = C₁ : Set   (not in scope, irrelevant)
-- B = B₁ : Set   (not in scope)
-- A = A₁ : Set   (not in scope)


-- Don't show irrelevance in irrelevant goal!

@irr IrrGoal :
  (        A : Set)
  (@0      B : Set)
  (@irr    C : Set)
  (@0 @irr D : Set)
  (@shirr  E : Set)
  (        A : Set)
  (@0      B : Set)
  (@irr    C : Set)
  (@0 @irr D : Set)
  (@shirr  E : Set)
  → Set
IrrGoal A B C D E = λ A B C D E → {!!}

-- Goal: Set
-- ————————————————————————————————————————————————————————————
-- E      : Set
-- D      : Set   (erased)
-- C      : Set
-- B      : Set   (erased)
-- A      : Set
-- E = E₁ : Set   (not in scope)
-- D = D₁ : Set   (not in scope, erased)
-- C = C₁ : Set   (not in scope)
-- B = B₁ : Set   (not in scope, erased)
-- A = A₁ : Set   (not in scope)


-- Don't show shape-irrelevance in shape-irrelevant goal!

@shirr ShIrrGoal :
  (        A : Set)
  (@0      B : Set)
  (@irr    C : Set)
  (@0 @irr D : Set)
  (@shirr  E : Set)
  (        A : Set)
  (@0      B : Set)
  (@irr    C : Set)
  (@0 @irr D : Set)
  (@shirr  E : Set)
  → Set
ShIrrGoal A B C D E = λ A B C D E → {!!}

-- Goal: Set
-- ————————————————————————————————————————————————————————————
-- E      : Set
-- D      : Set   (erased, irrelevant)
-- C      : Set   (irrelevant)
-- B      : Set   (erased)
-- A      : Set
-- E = E₁ : Set   (not in scope)
-- D = D₁ : Set   (not in scope, erased, irrelevant)
-- C = C₁ : Set   (not in scope, irrelevant)
-- B = B₁ : Set   (not in scope, erased)
-- A = A₁ : Set   (not in scope)
