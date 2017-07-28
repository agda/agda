-- Andreas, 2013-11-07
-- Instance candidates are now considered modulo judgemental equality.

module Issue899 where

postulate
  A B : Set
  f : {{ x : A }} → B
  instance a : A

instance
  a' : A
  a' = a

test : B
test = f

{- The previous code fails with the following message:

  Resolve implicit argument _x_257 : A. Candidates: [a : A, a : A]

There are indeed two values in scope of type A (a and a'), but given
that they are definitionally equal, Agda should not complain about it
but just pick any one of them.  -}

-- Andreas, 2017-07-28: the other example now also works, thanks to G. Brunerie

record Eq (A : Set) : Set₁ where
  field
    _==_ : A → A → Set

record Ord (A : Set) : Set₁ where
  field
    {{eq}} : Eq A
    _<_ : A → A → Set

postulate
  N : Set
  eqN : N → N → Set
  ordN : N → N → Set

instance
  EqN : Eq N
  EqN = record {_==_ = eqN}

  OrdN : Ord N
  OrdN = record {_<_ = ordN}

  ordToEq : {A : Set} → Ord A → Eq A
  ordToEq o = Ord.eq o

postulate
  f2 : (A : Set) {{e : Eq A}} → Set → Set

test2 = f2 N N
