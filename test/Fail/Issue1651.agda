-- Andreas, 2015-09-18, issue reported by Guillaume Brunerie

{-# OPTIONS --rewriting #-}

data _==_ {A : Set} (a : A) : A → Set where
  idp : a == a
{-# BUILTIN REWRITE _==_ #-}

postulate
  A : Set
  a b : A

r : a == b
{-# REWRITE r #-}
r = idp

-- Should not work, as this behavior is confusing the users.
-- Instead, should give an error that rewrite rule
-- can only be added after function body.
