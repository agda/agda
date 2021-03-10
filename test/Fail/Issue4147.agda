{-# OPTIONS --rewriting --confluence-check #-}

data _==_ {i} {A : Set i} : (x y : A) → Set i where
  refl : {a : A} → a == a

{-# BUILTIN REWRITE _==_ #-}

data ⊥ : Set where

record ⊤ : Set where
  constructor tt

module Test (p : ⊥ == ⊤) where
  abstract
    A : Set
    A = ⊥

    q : A == ⊤
    q = p

    {-# REWRITE q #-}

  f : A
  f = tt

  abstract
    g : ⊥
    g = f
    -- g reduces to tt, which does not have type ⊥.
