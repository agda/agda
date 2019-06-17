{-# OPTIONS --rewriting --confluence-check #-}

-- 2014-05-27 Jesper and Andreas

postulate
  A B : Set
  R   : A → B → Set

{-# BUILTIN REWRITE R #-}
