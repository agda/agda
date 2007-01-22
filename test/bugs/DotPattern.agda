module Bug where

data A : Set where
  a : A

h : A -> A
h a = a

data B : A -> Set where
  b : (x : A) -> B (h x)

data _==_ : {x₁ x₂ : A} -> B x₁ -> B x₂ -> Set where
  eqb : {x : A} -> b x == b x

-- The problem here is that we get the constraint h x = h x, which when x is a
-- meta variable we don't solve. This constraint blocks the solution y := b x
-- and so we don't see that y should be dotted. Either explicitly dotting y or
-- binding x removes the problem.
bad : {x : A}{y : B x} -> y == y -> A
bad eqb = ?
-- bad .{h x} .{b x} (eqb {x}) = ?    -- works
-- bad .{y = _} eqb	       = ?    -- works
-- bad (eqb {_})	       = ?    -- works

-- TODO: find example where syntactic equality wouldn't solve the problem.


