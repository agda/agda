
open import Agda.Builtin.Equality

postulate
  A : Set

id : A → A
id x = x

mutual
  ?Y : A → A → A
  ?Y = _

  ?X : A → A → A
  ?X = _

  -- This tries to solve ?X x x := ?Y x y, which fails but prunes
  -- ?Y x y := ?Z x. Failing ?X := ?Y we then try the other direction
  -- without realising that ?Y has been instantiated and (re)solve
  -- ?Y x y := ?X x x, leaving ?Z hanging!
  -- The `id` call is to make sure we get into `compareAtom`. The
  -- corresponding code in `compareTerm` does the right thing.
  constr₁ : ∀ x y → id (?X x x) ≡ id (?Y x y)
  constr₁ x y = refl

  -- We can then solve ?X.
  constr₂ : ∀ x y → ?X x y ≡ x
  constr₂ x y = refl

-- And check that they really are solved

checkY : ?Y ≡ λ x y → x
checkY = refl

checkX : ?X ≡ λ x y → x
checkX = refl

-- ...but we still have ?Z unsolved.
