-- Andreas, 2015-09-18 Andreas, issue reported by Gillaume Brunerie

{- Problem WAS

The following code doesn’t typecheck but it should. I have no idea what’s going on.

Replacing the definition of PathOver-rewr by a question mark and
asking for full normalisation of the goal (C-u C-u C-c C-t), I obtain
HetEq idp u v == (u == v), so it seems that the term PathOver (λ _ →
B) p u v) is rewritten as HetEq idp u v using ap-cst (as expected),
but then for some reason HetEq idp u v isn’t reduced to u == v. -}


{-# OPTIONS --rewriting --confluence-check #-}
-- {-# OPTIONS --show-implicit #-}

data _==_ {i} {A : Set i} (a : A) : A → Set where
  idp : a == a
{-# BUILTIN REWRITE _==_ #-}

ap : ∀ {i j} {A : Set i} {B : Set j} (f : A → B) {x y : A}
  → x == y → f x == f y
ap f idp = idp

ap-cst : ∀ {a} {b} {A : Set a} {B : Set b} (b : B) {x y : A} (p : x == y)
  → ap (λ _ → b) p == idp
ap-cst b idp = idp
{-# REWRITE ap-cst #-}

HetEq : {A B : Set} (e : A == B) (a : A) (b : B) → Set
HetEq idp a b = (a == b)

PathOver : {A : Set} (B : A → Set)
  {x y : A} (p : x == y) (u : B x) (v : B y) → Set
PathOver B p u v = HetEq (ap B p) u v

PathOver-rewr : {A B : Set} {x y : A} (p : x == y) (u v : B)
  → (PathOver (λ _ → B) p u v) == (u == v)
PathOver-rewr p u v = idp
