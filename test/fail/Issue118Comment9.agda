
module Issue118Comment9 where

open import Common.Level
open import Common.Coinduction

data Box (A : Set) : Set where
  [_] : A → Box A

postulate I : Set

data P : I → Set where
  c : ∀ {i} → Box (∞ (P i)) → P i

F : ∀ {i} → P i → I
F (c x) = _

G : ∀ {i} → Box (∞ (P i)) → I
G [ x ] = _

mutual

  f : ∀ {i} (x : P i) → P (F x)
  f (c x) = c (g x)

  g : ∀ {i} (x : Box (∞ (P i))) → Box (∞ (P (G x)))
  g [ x ] = [ ♯ f (♭ x) ]

-- The code above type checks, but the termination checker should
-- complain because the inferred definitions of F and G are
-- F (c x) = G x and G [ x ] = F (♭ x), respectively.

-- 2011-04-12 freezing: now the meta-variables remain uninstantiated.
-- good.
