{-# OPTIONS --guardedness-preserving-type-constructors #-}
module Issue602 where

infixl 6 _⊔_

postulate
  Level : Set
  zero  : Level
  suc   : Level → Level
  _⊔_   : Level → Level → Level

{-# BUILTIN LEVEL     Level #-}
{-# BUILTIN LEVELZERO zero  #-}
{-# BUILTIN LEVELSUC  suc   #-}
{-# BUILTIN LEVELMAX  _⊔_   #-}

infix 1000 ♯_

postulate
  ∞  : ∀ {a} (A : Set a) → Set a
  ♯_ : ∀ {a} {A : Set a} → A → ∞ A
  ♭  : ∀ {a} {A : Set a} → ∞ A → A

{-# BUILTIN INFINITY ∞  #-}
{-# BUILTIN SHARP    ♯_ #-}
{-# BUILTIN FLAT     ♭  #-}

data CoNat : Set0 where
  z : CoNat
  s : ∞ CoNat → CoNat

record A : Set2 where
  field
    f : Set1

record B (a : ∞ A) : Set1 where
  field
    f : A.f (♭ a)

postulate
  a : A

e : CoNat → A
e z = a
e (s n) = record
  { f = B (♯ e (♭ n))
  }