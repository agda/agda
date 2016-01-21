-- Andreas, 2016-01-21, issue 1791
-- With-clause stripping for copatterns with "polymorphic" field.

-- {-# OPTIONS --show-implicit #-}
-- {-# OPTIONS -v tc.with.strip:60 #-}

postulate anything : ∀{A : Set} → A

record Wrap (A : Set) : Set where
  field unwrap : A

module VisibleWorks where

  -- monomorphic field

  record Pointed (M : Set → Set) : Set₁ where
    field point : ∀ A → M A

  test : Pointed Wrap
  Wrap.unwrap (Pointed.point test A) with Set₂
  ... | _ = anything

-- polymorphic field

record Pointed (M : Set → Set) : Set₁ where
  field point : ∀{A} → M A

module ExplicitWorks where

  test : Pointed Wrap
  Wrap.unwrap (Pointed.point test {A}) with Set₂
  ... | _ = anything

-- WAS: hidden fails

test : Pointed Wrap
Wrap.unwrap (Pointed.point test) with Set₂
... | _ = anything

-- should succeed
