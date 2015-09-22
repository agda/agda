{-# OPTIONS --rewriting #-}

-- 2015-02-17 Jesper and Andreas

postulate
  A : Set
  R : A → A → Set
  f : A → A
  g : A → A
  r : R (f _) (g _)

{-# BUILTIN REWRITE R #-}
{-# REWRITE r #-}
