-- Andrea(s), 2016-07-06, issue #2076 reported by Andrea
-- This is to test printing of extended lambdas

-- {-# OPTIONS -v tc.cc:60 -v tc.term.exlam:100 -v reify.clause:60 #-}

postulate
  A : Set
  _,_ : A → A → A

data Unit : Set where
  true : Unit

bar : (p : A) (q : A) → Unit → A
bar p q = aux
  where
  aux : Unit → A
  aux true = p , q

foo : (p : A) (q : A) → Unit → A
foo p q = \ { true → p , q}

test : (a : A) → Unit → A
test a = foo a a
-- Normalize me! Expected:
-- λ a → λ { true → a , a }

-- From test/interaction/ExtendedLambdaCase.agda

data Bool : Set where
  true false : Bool

data Void : Set where

module M {A : Set}(B : A → Set) where
  postulate
    Bar : (Bool → Bool) → Set

Test : Set
Test = (y : Bool) → M.Bar {Bool} (λ _ → Void) (λ { true → true ; false → false })
-- Normalize me! Expected:
-- (y : Bool) → M.Bar (λ _ → Void) (λ { true → true ; false → false })

-- .extendedlambda1 y true  = true
-- .extendedlambda1 y false = false
-- dropped args:  []
-- hidden  args:  []
-- visible args:  [y]

-- Extended lambda inside parameterized module

module PM (X : Set) where
  extlam : (p : A) (q : A) → Unit → A
  extlam p q = \ { true -> p , q}

-- ConcreteDef extended lambda's implementation ".extendedlambda1" has type:
-- Unit → A
-- dropped args:  [X]
-- hidden  args:  []
-- visible args:  [p, q]

-- clauses before compilation .extendedlambda1 p₁ q₁ true = p₁ , q₁

  -- , clauseTel =
  --   ExtendTel r(El {_getSort = Type (Max [ClosedLevel 1]), unEl = Sort (Type (Max []))}) (Abs "X"
  --   ExtendTel r(El {_getSort = Type (Max []), unEl = Def Issue2076.A []}) (Abs "p"
  --   ExtendTel r(El {_getSort = Type (Max []), unEl = Def Issue2076.A []}) (Abs "q"
  --   EmptyTel)))
  -- , namedClausePats =
  --   [r(X = VarP (DBPatVar {dbPatVarName = "X", dbPatVarIndex = 2}))
  --   ,r(p = VarP (DBPatVar {dbPatVarName = "p", dbPatVarIndex = 1}))
  --   ,r(q = VarP (DBPatVar {dbPatVarName = "q", dbPatVarIndex = 0}))
  --   ,r(x = ConP Issue2076.Unit.true(inductive)[] (ConPatternInfo {conPRecord = Nothing, conPType = Just r(El {_getSort = Type (Max []), unEl = Def Issue2076.Unit []})}) [])
  --   ]
  -- , clauseBody = Bind (Abs "h0" Bind (Abs "h1" Bind (Abs "h2" Body (Def Issue2076._,_ [Apply r(Var 1 []),Apply r(Var 0 [])]))))

-- clauses before compilation
--   , clauseTel =
--     ExtendTel r(El {_getSort = Type (Max [ClosedLevel 1]), unEl = Sort (Type (Max []))}) (Abs "X"
--     ExtendTel r(El {_getSort = Type (Max []), unEl = Def Issue2076.A []}) (Abs "p"
--     ExtendTel r(El {_getSort = Type (Max []), unEl = Def Issue2076.A []}) (Abs "q"
--     EmptyTel)))

--   , namedClausePats =
--     [r(X = VarP (DBPatVar {dbPatVarName = "X", dbPatVarIndex = 2}))
--     ,r(p = VarP (DBPatVar {dbPatVarName = "p", dbPatVarIndex = 1}))
--     ,r(q = VarP (DBPatVar {dbPatVarName = "q", dbPatVarIndex = 0}))]

--   , clauseBody = Bind (Abs "h0" Bind (Abs "h1" Bind (Abs "h2"
--       Body (Def Issue2076.PM..extendedlambda1
--         [Apply r(Var 2 []),Apply r(Var 1 []),Apply r(Var 0 [])]))))

  -- wrong printing
  -- clauses before compilation extlam p q = λ { q₁ true → p₁ , q₁ }

  inside : (a : A) → Unit → A
  inside a = extlam a a

  bla : (a : A) → {!!}
  bla a = {!inside a!}
  -- Normalization of `inside a` here should yield
  -- λ { true → a , a }

ptest : (a : A) → Unit → A
ptest a = PM.extlam Unit a a
-- ptest should normalize to λ a → λ { true → a , a }

module MM (Y : Set) where
  open PM Y public

-- Normalizing MM.extlam should yield
-- λ Y p q → λ { true → p , q }

open MM Unit

opentest : (a : A) → Unit → A
opentest a = extlam a a
-- opentest should normalize to λ a → λ { true → a , a }

module Parent (Y : Set) where
  module Child (X : Set) where
    extlam2 : (p : A) (q : A) → Unit → A
    extlam2 p q = \ { true -> p , q}

-- Normalizing Parent.Child.extlam2 should yield
-- λ Y X p q → λ { true → p , q }

open import Agda.Builtin.Nat

data Vec (A : Set) : Nat → Set where
  [] : Vec A 0
  _∷_ : ∀ {n} → A → Vec A n → Vec A (suc n)

postulate
  h : (∀ {n} → Vec Nat n → Nat) → Nat

f : Nat → Nat
f n = h λ where []       → 0
                (x ∷ xs) → n

-- Normalising f should yield
-- λ n → h (λ { [] → 0 ; (x ∷ xs) → n })

-- Andreas, 2020-06-24, issue #4775
-- After fixing a bug in the unifier which assigned
-- conPRecord = True to a data constructor like suc,
-- the output has changed to:
--
-- λ n → h (λ { [] → 0 ; {suc n₁} (x ∷ xs) → n })
--
-- This should be investigated.  Similar effect for
-- interaction/ExpandEllipsis
