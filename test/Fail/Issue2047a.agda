open import Common.Equality

data Bool : Set where
  true false : Bool

data IsTrue : Bool → Set where
  itis : IsTrue true

module M (u : Bool) where
  foo bar : (p : IsTrue u) → Bool
  foo = \ { itis → true  }
  bar = \ { itis → false }

test : ∀ u → M.foo u ≡ M.bar u
test u = refl

-- Trigger printing of the extended lambdas.

-- Ideally, this would not show the internal names, like in
--
--   .Issue2047a.M..extendedlambda0 u p !=
--   .Issue2047a.M..extendedlambda1 u p of type Bool
--   when checking that the expression refl has type M.foo u ≡ M.bar u
--
-- but rather show
--
--   (\ { itis → true  }) .p != (\ { itis → false }) .p
