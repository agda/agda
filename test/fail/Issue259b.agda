-- Note: It would be good if the code below type checked, this file
-- documents that it doesn't.

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
