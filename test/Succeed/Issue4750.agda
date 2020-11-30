
open import Agda.Builtin.Nat
open import Agda.Builtin.Equality

data Three : Set -- (AAA) To fix things, move this line...

data One : Set where
  one : Nat → One

data Two : Set where
  two : One → Two

lemma′ : ∀ (m n : Nat) → (one m) ≡ (one n) → m ≡ n
lemma′ m .m refl = refl

lemma : ∀ (m n : Nat) → (two (one m)) ≡ (two (one n)) → m ≡ n
lemma m .m refl = refl
{- Error was:
I'm not sure if there should be a case for the constructor refl,
because I get stuck when trying to solve the following unification
problems (inferred index ≟ expected index):
  two (one m) ≟ two (one n)
when checking that the pattern refl has type
two (one m) ≡ two (one n)
-}

-- (BBB) ... to here.

data Three where
  three : Three
