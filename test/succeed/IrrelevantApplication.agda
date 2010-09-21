-- 2010-09-06 Andreas

module IrrelevantApplication where

-- an unknown function that does not use its second argument

postulate
  f : {A B : Set} -> A -> .B -> A

data _==_ {A : Set}(a : A) : A -> Set where
  refl : a == a

-- the second argument is irrelevant for equality

proofIrr : {A : Set}{x y z : A} -> f x y == f x z
proofIrr = refl

-- irrelevant arguments (like x) may appear as arguments to irrelevant func.s

id : {A B : Set} -> (.A -> B) -> .A -> B
id g x = g x

pId : {A : Set} -> A -> A
pId x = x

-- t = pId id

record Prod (A B : Set) : Set where
  constructor _,_
  field
    fst : A
    snd : B

-- matching an irrelevant record is ok as long as fields are use irrelevantly
irrElim : {A B C : Set} → .(Prod A B) → (.A → .B → C) → C
irrElim (a , b) f = f a b

lemma : {A B C : Set}(a : A)(b : B)(f : .A -> .B -> C) -> irrElim (a , b) f == f a b
lemma a b f = refl
