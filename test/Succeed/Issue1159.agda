-- Andreas, 2016-02-02, issues 480, 1159, 1811

data Unit : Set where
  unit : Unit

-- To make it harder for Agda, we make constructor unit ambiguous.
data Ambiguous : Set where
  unit : Ambiguous

postulate
  f : ∀{A : Set} → (A → A) → A

test : Unit
test = f \{ unit → unit }

-- Extended lambda checking should be postponed until
-- type A has been instantiated to Unit.

-- Should succeed.
