-- Andreas, 2019-04-10, issue #3687, name mayhem when printing module contents (C-c C-o)

-- {-# OPTIONS -v interaction.contents.record:20 #-}

record Cat : Set₁ where
  field
    Obj   : Set
    Hom   : (A B : Obj) → Set
    Eq    : ∀{A B} (f g : Hom A B) → Set
    id    : (A : Obj) → Hom A A
    comp  : ∀{A B C} (f : Hom B C) (g : Hom A B) → Hom A C

record Functor (C1 C2 : Cat) : Set where

record FunEq {C D : Cat} (F G : Functor C D) : Set₁ where
  field
    eqMap : ∀{c d} (f g : Cat.Hom C c d) (eq : Cat.Eq C f g) → Set

test : ∀ C D (F G : Functor C D) → FunEq F G
FunEq.eqMap (test C D F G) f g f=g = {!D!}  -- C-c C-o

-- In the output, the names are completely garbled:

-- Names
--   Obj  : Set
--   Hom  : f=g → f=g → Set
--   Eq   : {A B : g} → f=g A B → f=g A B → Set
--   id   : (A : f) → g A A
--   comp : {A B : d} {C = C₁ : d} → f B C₁ → f A B → f A C₁

-- test/interaction$ make AGDA_BIN=agda-2.5.1.1 Issue3687.cmp
