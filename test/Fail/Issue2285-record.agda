-- Andreas, 2016-11-02, issue #2285
-- double check for record types

record Big : _ where
  field any : ∀{a} → Set a
