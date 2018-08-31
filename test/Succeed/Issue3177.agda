
open import Agda.Builtin.Equality

postulate
   A : Set

Phantom : A → Set
Phantom _ = A

postulate
  rigid : A → A

mutual
  X : A → A → A → A
  X = _

  Y : (x y : A) → Phantom x
  Y = _

  -- This constraint triggers pruning of X in an attempt to remove the non-linearity.
  -- It doesn't get rid of the non-linearity but prunes x setting X x y z := Z y z,
  -- for a fresh meta Z.
  c₁ : (x y : A) → X x y y ≡ rigid y
  c₁ x y = refl

  -- Here we end up with Z y z == rigid (Y x y) which requires pruning x from Y. This
  -- fails due to the phantom dependency on x in the type of Y and the constraint is
  -- left unsolved. If we hadn't pruned x from X we could have solved this with
  -- X x y z := rigid (Y x y), turning the first constraint into rigid (Y x y) == rigid y,
  -- which is solved by Y x y := y.
  c₂ : (x y z : A) → X x y z ≡ rigid (Y x y)
  c₂ x y z =  refl
