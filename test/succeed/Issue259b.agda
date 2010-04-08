
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

-- Bug.agda:20,8-12
-- i' != i of type T x
-- when checking that the pattern c .i has type D (c (λ {.x} → i))