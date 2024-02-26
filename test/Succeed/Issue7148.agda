-- Andreas, 2024-02-26, issue #7148, regression in 2.6.4.2.
-- Original test case by mechvel.
-- 'with'-abstraction failed here due to lack of eta-contraction.

data _≡_ {A : Set} (x : A) : A → Set where
  refl : x ≡ x

record Wrap (A : Set) : Set where
  -- pattern; no-eta-equality   -- can't turn off eta
  constructor wrap
  field wrapped : A

data Dec (A : Set) : Set where
  no : Dec A

postulate
  foo : ∀{A : Set}{P : A → Set} → (∀ x → Dec (P x)) → ∀ x → Dec (P x)
    -- can't inline P = LtWrap
    -- can't define foo = id
  Nat : Set
  P   : Nat → Set
  p?  : ∀ x → Dec (P x)

-- can't make these postulates
PWrap : Wrap Nat → Set
PWrap (wrap f) = P f

pWrap? : ∀ p → Dec (PWrap p)
pWrap? (wrap f) = p? f

bar : Wrap Nat → Wrap Nat
bar fs with foo pWrap? fs
... | no = fs

test : ∀ fs → bar fs ≡ fs
test fs with foo pWrap? fs
... | no = refl

-- Should succeed.
