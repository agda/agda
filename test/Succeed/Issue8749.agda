-- Andreas, 2026-09-15, issue #8749, shrunk from a standard library example
-- using `Data.Nat.Solver`.
--
-- A numeral like `1` elaborates to `fromNat 1 {{i}} {{c}}` with instance metas
-- `i : Number Nat` and `c : Constraint 1`.  While the arguments of
-- `solve 1 refl` are checked, instance search is postponed
-- (`postponeInstanceConstraints`), so `i` is unsolved and the expected type
-- `Hidden (fromNat 1 {{i}} {{c}})` of `refl` does not reduce.  Agda thus could
-- not see that a hidden lambda has to be inserted, checked `refl` against the
-- blocked type and postponed the resulting type comparison.  Once `i` was
-- solved, the type reduced to `{x : Nat} → …` and the comparison failed --
-- too late to insert the hidden lambda (a facet of issue #1079).
--
-- Now Agda runs the deferred instance search speculatively; since it reveals
-- that the type becomes a hidden function type, the whole type checking
-- problem is postponed instead.

open import Agda.Builtin.Equality
open import Agda.Builtin.FromNat
open import Agda.Builtin.Nat
open import Agda.Builtin.Unit

instance
  NumberNat : Number Nat
  NumberNat = record { Constraint = λ _ → ⊤; fromNat = λ n → n }

-- A miniature `Data.Vec.N-ary.∀ⁿʰ`: `n` nested hidden quantifiers.

Hidden : Nat → Set
Hidden zero    = 0 ≡ 0
Hidden (suc n) = {x : Nat} → Hidden n

-- A miniature `Relation.Binary.Reflection.solve`.

solve : (n : Nat) → Hidden n → Set
solve n hyp = Nat

-- This always worked: the hidden lambda is already there.

good : Set
good = solve 1 λ {_} → refl

-- This used to fail:

bad : Set
bad = solve 1 refl

------------------------------------------------------------------------
-- The same problem without numerals: any postponed instance meta will do.

record Cls (A : Set) : Set where
  field val : A
open Cls {{...}}

instance
  clsNat : Cls Nat
  clsNat = record { val = suc zero }

bad' : Set
bad' = solve val refl
