-- Andreas, 2018-05-09, issue 2636, reported by nad

-- {-# OPTIONS -v tc.pos:10 #-}

id : (A : Set₁) → A → A
id A x = x

A : Set₁
A = Set
  where
  F : Set₁ → Set₁
  F X = X

  data D : Set₁ where
    c : F D → D

  lemma : F (D → Set) → D → Set
  lemma fp d = id (F (D → Set)) fp d

-- Problem was:
-- Positivity checker for D complained when lemma was present.
