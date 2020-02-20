-- Andreas, 2019-06-26, issue #3855
-- Mark erased hypotheses as such in a non-erased goal.
-- Same for irrelevance.

Goal :
  (        A : Set)
  (@0      B : Set)
  (@irr    C : Set)
  (@0 @irr D : Set)
  (        A : Set)
  (@0      B : Set)
  (@irr    C : Set)
  (@0 @irr D : Set)
  → Set
Goal A B C D = λ A B C D → {!!}

-- Goal: Set
-- ————————————————————————————————————————————————————————————
-- D      : Set  (erased, irrelevant)
-- C      : Set  (irrelevant)
-- B      : Set  (erased)
-- A      : Set
-- D = D₁ : Set  (not in scope, erased, irrelevant)
-- C = C₁ : Set  (not in scope, irrelevant)
-- B = B₁ : Set  (not in scope, erased)
-- A = A₁ : Set  (not in scope)


-- Don't show erasure in erased goal!

@0 ErasedGoal :
  (        A : Set)
  (@0      B : Set)
  (@irr    C : Set)
  (@0 @irr D : Set)
  (        A : Set)
  (@0      B : Set)
  (@irr    C : Set)
  (@0 @irr D : Set)
  → Set
ErasedGoal A B C D = λ A B C D → {!!}

-- Goal: Set
-- ————————————————————————————————————————————————————————————
-- D      : Set  (irrelevant)
-- C      : Set  (irrelevant)
-- B      : Set
-- A      : Set
-- D = D₁ : Set  (not in scope, irrelevant)
-- C = C₁ : Set  (not in scope, irrelevant)
-- B = B₁ : Set  (not in scope)
-- A = A₁ : Set  (not in scope)


-- Don't show irrelevance in irrelevant goal!

@irr IrrGoal :
  (        A : Set)
  (@0      B : Set)
  (@irr    C : Set)
  (@0 @irr D : Set)
  (        A : Set)
  (@0      B : Set)
  (@irr    C : Set)
  (@0 @irr D : Set)
  → Set
IrrGoal A B C D = λ A B C D → {!!}

-- Goal: Set
-- ————————————————————————————————————————————————————————————
-- D      : Set  (erased)
-- C      : Set
-- B      : Set  (erased)
-- A      : Set
-- D = D₁ : Set  (not in scope, erased)
-- C = C₁ : Set  (not in scope)
-- B = B₁ : Set  (not in scope, erased)
-- A = A₁ : Set  (not in scope)
