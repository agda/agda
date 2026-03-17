-- The "intro" command manages to refine goals of type ∞ A with the
-- term ♯ ?.

{-# OPTIONS --erasure #-}

module IntroSharp where

postulate
  ∞  : ∀ {@0 a} (A : Set a) → Set a
  ♯_ : ∀ {@0 a} {A : Set a} → A → ∞ A
  ♭  : ∀ {@0 a} {A : Set a} → ∞ A → A

{-# BUILTIN INFINITY ∞  #-}
{-# BUILTIN SHARP    ♯_ #-}
{-# BUILTIN FLAT     ♭  #-}

Foo : ∞ Set
Foo = ?
