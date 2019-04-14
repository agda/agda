-- Andreas, 2019-03-18, AIM XXIX, performance regression in 2.5.4
-- The following was quick in 2.5.3

postulate
  Bool : Set
  Foo : Bool → Bool → Bool → Bool → Bool → Bool → Bool → Bool → Bool → Set

data FooRel
  : (x1 x1' : Bool)
    (x2 x2' : Bool)
    (x3 x3' : Bool)
    (x4 x4' : Bool)
    (x5 x5' : Bool)
    (x6 x6' : Bool)
    (x7 x7' : Bool)
    (x8 x8' : Bool)
    (x9 x9' : Bool)
  → Foo x1 x2 x3 x4 x5 x6 x7 x8 x9
  → Foo x1' x2' x3' x4' x5' x6' x7' x8' x9'
  → Set
  where
  tran
    : (x1 x1' x1'' : Bool)
      (x2 x2' x2'' : Bool)
      (x3 x3' x3'' : Bool)
      (x4 x4' x4'' : Bool)
      (x5 x5' x5'' : Bool)
      (x6 x6' x6'' : Bool)
      (x7 x7' x7'' : Bool)
      (x8 x8' x8'' : Bool)
      (x9 x9' x9'' : Bool)
      (t : Foo x1 x2 x3 x4 x5 x6 x7 x8 x9)
      (t' : Foo x1' x2' x3' x4' x5' x6' x7' x8' x9')
      (t'' : Foo x1'' x2'' x3'' x4'' x5'' x6'' x7'' x8'' x9'')
    → FooRel x1 x1' x2 x2' x3 x3' x4 x4' x5 x5' x6 x6' x7 x7' x8 x8' x9 x9' t t'
    → FooRel x1' x1'' x2' x2'' x3' x3'' x4' x4'' x5' x5'' x6' x6'' x7' x7'' x8' x8'' x9' x9'' t' t''
    → FooRel x1 x1'' x2 x2'' x3 x3'' x4 x4'' x5 x5'' x6 x6'' x7 x7'' x8 x8'' x9 x9'' t t''

foo
  : (x1 x1' : Bool)
    (x2 x2' : Bool)
    (x3 x3' : Bool)
    (x4 x4' : Bool)
    (x5 x5' : Bool)
    (x6 x6' : Bool)
    (x7 x7' : Bool)
    (x8 x8' : Bool)
    (x9 x9' : Bool)
    (t : Foo x1 x2 x3 x4 x5 x6 x7 x8 x9)
    (t' : Foo x1' x2' x3' x4' x5' x6' x7' x8' x9')
  → FooRel x1 x1' x2 x2' x3 x3' x4 x4' x5 x5' x6 x6' x7 x7' x8 x8' x9 x9' t t'
  → Set
foo x1 x1' x2 x2' x3 x3' x4 x4' x5 x5' x6 x6' x7 x7' x8 x8' x9 x9' t t' (tran .x1 x1'' .x1' .x2 x2'' .x2' .x3 x3'' .x3' .x4 x4'' .x4' .x5 x5'' .x5' .x6 x6'' .x6' .x7 x7'' .x7' .x8 x8'' .x8' .x9 x9'' .x9' .t t'' .t' xy yz) = Bool

-- Should check quickly again in 2.6.0
