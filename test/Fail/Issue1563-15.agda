{-# OPTIONS --rewriting #-}

data _==_ {A : Set} (a : A) : A → Set where
  idp : a == a
{-# BUILTIN REWRITE _==_ #-}

ap : {A B : Set} (f : A → B) {x y : A}
  → x == y → f x == f y
ap f idp = idp

postulate
  Circle : Set
  base : Circle
  loop : base == base

module _ (A : Set) (base* : A) (loop* : base* == base*) where
  postulate
    Circle-rec : Circle → A
    Circle-base-β : Circle-rec base == base*
  {-# REWRITE Circle-base-β #-}
  postulate
    Circle-loop-β : ap Circle-rec loop == loop*
  {-# REWRITE Circle-loop-β #-}

test : (x : Circle) → ap (Circle-rec (Circle → Circle) (λ y → y) idp x) loop == idp
test x = idp

{-
An internal error has occurred. Please report this as a bug.
Location of the error: src/full/Agda/TypeChecking/Rewriting/NonLinMatch.hs:178
-}
