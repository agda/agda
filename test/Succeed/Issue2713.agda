
{-# OPTIONS --instance-search-depth=10 #-}

open import Agda.Primitive

it : ∀ {a} {A : Set a} {{x : A}} -> A
it {{x}} = x

infixr 5 _,_
postulate
  Pair : ∀ {a} (A : Set a) {b} (B : Set b) -> Set (a ⊔ b)
  _,_  : ∀ {a} {A : Set a} {b} {B : Set b} -> A -> B -> Pair A B

data Constraint {a} {A : Set a} (x : A) : Set where
  mkConstraint : Constraint x

record Inner {l a} {A : Set a} (x : A) (_ : Constraint x) (C : Set l) : Set l where
  field
    value : C

Class : ∀ {l a} {A : Set a} (x : A) (C : Set l) -> Set l
Class x C = Inner x mkConstraint C

FunctionClass = λ
  {a} (A : Set a)
  -> Class A (A -> A)

DiagonalClass = λ
  {i} {I : Set i}
  {r} (R : I -> I -> Set r)
  x
  -> Class (R , x) (R x x)

DiagonalFunctionClass = λ
  {i} {I : Set i}
  {r} (R : I -> I -> Set r)
  x
  -> Class (R , x) (R x x -> R x x)

postulate
  toDiagonalFunctionClass : ∀
    {i} {I : Set i}
    {r} {R : I -> I -> Set r}
    {{iD : ∀ {x} -> DiagonalClass R x}}
    -> ∀ {x} -> DiagonalFunctionClass R x

DiagonalPropertyType = λ
  {i r p} {I : Set i}
  (R : I -> I -> Set r)
  (P : ∀ x -> R x x -> Set p)
  -> ∀ x (d : R x x) -> P _ d

DiagonalPropertyClass = λ
  {i r p} {I : Set i}
  (R : I -> I -> Set r)
  (P : ∀ x -> R x x -> Set p)
  (C : FunctionClass I)
  -> Class (R , P , C) (DiagonalPropertyType R P)

diagonalProperty : ∀
  {i r p} {I : Set i}
  {R : I -> I -> Set r}
  {P : ∀ x -> R x x -> Set p}
  {{C : FunctionClass I}}
  {{iDP : DiagonalPropertyClass R P C}}
  -> DiagonalPropertyType R P
diagonalProperty {{iDP = iDP}} = Inner.value iDP

-- works-1 works-2
fails : ∀
  {r p} {I : Set}
  {R : I -> I -> Set r}
  {P : ∀ x -> R x x -> Set p}
  (C : FunctionClass I)
  {{iDP : DiagonalPropertyClass R P C}}
  -> DiagonalPropertyType R P

-- works-1 C x d =
--   let instance iC = C
--   in diagonalProperty _ d

-- works-2 C x d =
--   let instance iC = C
--                iDF = toDiagonalFunctionClass
--   in diagonalProperty {{it}} _ d

fails C x d =
  let instance iC = C
               iDF = toDiagonalFunctionClass
  in diagonalProperty _ d -- Instance search depth exhausted
