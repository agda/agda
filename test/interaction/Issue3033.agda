-- Andreas, 2018-04-16, issue #3033, reported by Christian Sattler

-- The DotPatternCtx was not used inside dot patterns in ConcreteToAbstract.

postulate
  A : Set
  B : Set
  a : A
  f : A → B

data C : B → Set where
  c : C (f a)

foo : (b : B) → C b → Set
foo .{!f a!} c = A  -- give "f a" here

-- WAS: foo .f a c = A
-- NOW: foo .(f a) c = A
