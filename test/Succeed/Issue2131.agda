-- Andreas, 2016-08-08, issue #2131 reported by Andrea

{-# OPTIONS --allow-unsolved-metas #-}

-- {-# OPTIONS --show-irrelevant #-}
-- {-# OPTIONS -v tc:25 #-}

postulate
  A : Set
  P : (F : .(U : Set) → Set) → Set

const : (X : Set) .(Y : Set) → Set
const X Y = X

works : (G : .(Z : Set) → Set) (p : P G) → P (λ V → const (G _) V) -- V is irrelevant
works G p = p

irr : (G : .(Z : Set) → Set) (p : P G) → P (const (G {!!}))
irr G p = p

-- Agda computes as follows:
--   P G =? P (const (G (?0 G p))) : Set
--   G =? const (G (?0 G p)) : .(U : Set) → Set
--   G U =? const (G (?0 G p)) U : Set
--   G U =? G (?0 G p)
--   ?0 G p := U
-- This assignment fails, since U is not in scope of ?0
-- However, since ?0 is in irrelevant context, this should not be
-- a definite failure, but leave the meta unsolved.
