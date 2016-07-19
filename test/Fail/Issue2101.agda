-- Andreas, 2016-07-17 issue 2101

-- It should be possible to place a single function with a where block
-- inside `abstract`.

-- This will work if type signatures inside a where-block
-- are considered private, since in private type signatures,
-- abstract definitions are transparent.
-- (Unlike in public type signatures.)

record Wrap (A : Set) : Set where
  field unwrap : A

postulate
  P : ∀{A : Set} → A → Set

module AbstractPrivate (A : Set) where
  abstract
    B : Set
    B = Wrap A

    postulate
      b : B

    private -- this makes abstract defs transparent in type signatures
      postulate
        test : P (Wrap.unwrap b) -- should succeed


abstract

  unnamedWhere : (A : Set) → Set
  unnamedWhere A = A
    where  -- the following definitions are private!
    B : Set
    B = Wrap A

    postulate
      b : B
      test : P (Wrap.unwrap b) -- should succeed

  namedWherePrivate : (A : Set) → Set
  namedWherePrivate A = A
    module MP where
    B : Set
    B = Wrap A

    private
      postulate
        b : B
        test : P (Wrap.unwrap b) -- should succeed

  namedWhere : (A : Set) → Set
  namedWhere A = A
    module M where  -- the definitions in this module are not private!
    B : Set
    B = Wrap A

    postulate
      b : B
      test : P (Wrap.unwrap b) -- should fail!

access = M.b  -- should be in scope

outside : ∀ {A} → M.B A → A
outside = Wrap.unwrap  -- should fail and does so

--
