-- Note: It would be good if the code below type checked, this file
-- documents that it doesn't.

module Issue151a where

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
