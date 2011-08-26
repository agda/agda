{-# OPTIONS --universe-polymorphism #-}

module NoPanic where

postulate
  Level : Set
  lzero : Level
  lsuc  : Level → Level

{-# BUILTIN LEVEL     Level #-}
{-# BUILTIN LEVELZERO lzero #-}
{-# BUILTIN LEVELSUC  lsuc  #-}

module M {A : Set} where

  postulate
    I : A → ∀ a → Set a
    i : ∀ (x : A) {a} → I x a
    f : {B : Set} → B
    a : A

  Foo : Set₁
  Foo with i (f a)
  Foo | _ = Set

-- Old (bad) error message:

-- NoPanic.agda:24,3-16
-- Panic: Pattern match failure in do expression at
-- src/full/Agda/TypeChecking/Rules/Term.hs:646:7-18
-- when checking that the expression _22 {A} has type Level
