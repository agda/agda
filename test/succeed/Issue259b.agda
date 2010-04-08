
module Issue259b where

postulate
 R : Set
 T : R → Set

I : Set
I = {x : R} → T x  -- The code type checks if this Π is explicit.

data P : Set where
 c : I → P

data D : P → Set where
 c : (i : I) → D (c i)

-- When pattern matching we do want to eta contract implicit lambdas.
Foo : (i : I) → D (c i) → Set₁
Foo i (c .i) = Set

postulate
  A : Set
  a : A
  b : ({x : A} → A) → A
  C : A → Set

d : {x : A} → A
d {x} = a

e : A
e = b (λ {x} → d {x}) -- this shouldn't be eta contracted though

F : C e → Set₁
F _ with Set
F _ | _ = Set

-- Bug.agda:20,8-12
-- i' != i of type T x
-- when checking that the pattern c .i has type D (c (λ {.x} → i))