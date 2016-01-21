-- Andreas, 2016-01-21, issue 1791
-- With-clause stripping for copatterns with "polymorphic" field.

-- {-# OPTIONS -v tc.with.strip:60 #-}

postulate anything : ∀{A : Set} → A

record Wrap (A : Set) : Set where
  field unwrap : A

record Pointed (M : Set → Set) : Set₁ where
  field point : ∀{A} → M A  -- field type starts with hidden quantifier!

test : Pointed Wrap
Wrap.unwrap (Pointed.point test) with Set₂
... | _ = anything

-- should succeed
