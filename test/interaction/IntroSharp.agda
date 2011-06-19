-- The "intro" command manages to refine goals of type ∞ A with the
-- term ♯ ?.

{-# OPTIONS --universe-polymorphism #-}

module IntroSharp where

postulate
  Level : Set
  zero : Level
  suc  : (i : Level) → Level
  _⊔_ : Level -> Level -> Level

{-# BUILTIN LEVEL     Level #-}
{-# BUILTIN LEVELZERO zero  #-}
{-# BUILTIN LEVELSUC  suc   #-}
{-# BUILTIN LEVELMAX  _⊔_   #-}

postulate
  ∞  : ∀ {a} (A : Set a) → Set a
  ♯_ : ∀ {a} {A : Set a} → A → ∞ A
  ♭  : ∀ {a} {A : Set a} → ∞ A → A

{-# BUILTIN INFINITY ∞  #-}
{-# BUILTIN SHARP    ♯_ #-}
{-# BUILTIN FLAT     ♭  #-}

Foo : ∞ Set
Foo = ?
