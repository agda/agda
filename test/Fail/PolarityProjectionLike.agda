-- Andreas, 2015-06-29 polarity handling is broken
-- See also issue 1592

-- {-# OPTIONS -v tc.polarity:20 -v tc.proj.like:100 #-}
-- {-# OPTIONS -v tc.conv.elim:25 --show-implicit #-}

open import Common.Size
open import Common.Prelude

data D : Size → Set where
  c : ∀ i → D (↑ i)

record Type (a : Bool) : Set1 where
  constructor mkType
  field type : Set
open Type

Opp : Set → Set
Opp X = X → ⊥

-- projection-like contravariant function which does not unfold
abstract
  Contra : ∀ a (T : Type a) → Set
  Contra a (mkType A) = Opp A

-- Subtyping is broken for projection(-like) things.
-- This is exploitable as  Contra true (mkType X)  does not reduce to Opp X here.
cast : ∀{i} → Contra true (mkType (D i)) → Contra true (mkType (D (↑ i)))
cast x = x

-- Here it, does reduce.
abstract
  loop : ∀{i} → D i → ⊥
  loop (c i) = cast loop (c i)

absurd : ⊥
absurd = loop (c ∞)
