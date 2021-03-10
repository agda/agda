-- Andreas, 2019-11-11, issue #4189, reported by nad.

-- Record constructors living in the record module are problematic
-- as the record module is parameterized over the record value,
-- but the constructor not.

-- Thus, a record constructor does not live in the record module
-- any more.

-- {-# OPTIONS -v tc.mod.apply:100 #-}

record ⊤ : Set where
  constructor tt

module Unit = ⊤ renaming (tt to unit)
  -- WAS: internal error
  -- NOW: warning about tt not being in scope

tt′ : ⊤
tt′ = ⊤.tt
  -- WAS: success
  -- NOW: Not in scope: ⊤.tt
