-- Modified: Andreas, 2011-04-11 freezing metas
 
module Issue151 where

record A : Set₁ where
  field
    El : Set

data B (a : A) : Set₁ where
  b : ∀ a′ → B a′ → B a

data C a : B a → B a → Set₁ where
  c  : ∀ a′ (p : B a′) → C a (b record{ El = A.El a′ } p) (b a′ p)
  c′ : ∀ a′ (p : B a′) → C a (b a′ p) (b a′ p)

-- In order to type check the second clause the unifier
-- needs to eta contract the record in the target of the c
-- constructor.
foo : ∀ a (p : B a) (p′ : B a) → C a (b a p) p′ → Set₁
foo a p (b .a .p) (c′ .a .p) = Set
foo a p (b .a .p) (c .a .p)  = Set

postulate
  D : A → Set
  d : (a : A) → D a

-- The following definition generates a constraint
--   α record{ El = A.El a } == D a
-- on the metavariable above. To solve this the constraint
-- solver has to eta contract the record to see that the
-- left hand side is a proper Miller pattern.
bar : (test : (a : A) -> _) -> (a : A) → D a
bar test a = test record{ El = A.El a }
