open import Agda.Primitive
open import Agda.Builtin.Nat

Type : (i : Level) -> Set (lsuc i)
Type i = Set i

postulate
  P : (i : Level) (A : Type i) → A → Type i

postulate
  lemma : (a : Nat) -> P _ _ a
