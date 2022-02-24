{-# OPTIONS --syntactic-equality=2 --allow-unsolved-metas #-}

-- Limited testing suggests that --syntactic-equality=2 is a little
-- faster than --syntactic-equality=0 and --syntactic-equality=1 for
-- this file.

-- The option --allow-unsolved-metas and the open goal at the end of
-- the file ensure that time is not wasted on serialising things.

open import Agda.Builtin.Equality

data D : Set where
  c : D

data Delay-D : Set where
  now   : D → Delay-D
  later : Delay-D → Delay-D

-- The result of f x is 5000 applications of later to now x.

f : D → Delay-D
f x =
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  later (later (later (later (later (later (later (later (later (later (
  now x
  ))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  ))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  ))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  ))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  ))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  ))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  ))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  ))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  ))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  ))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  ))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  ))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  ))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  ))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  ))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  ))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  ))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  ))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  ))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  ))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  ))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  ))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  ))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  ))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  ))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  ))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  ))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  ))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  ))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  ))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  ))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  ))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  ))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  ))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  ))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  ))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  ))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  ))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  ))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  ))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  ))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  ))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  ))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  ))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  ))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  ))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  ))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  ))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  ))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  ))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  ))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  ))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  ))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  ))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  ))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  ))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  ))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  ))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  ))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  ))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  ))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  ))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  ))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  ))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  ))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  ))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  ))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  ))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  ))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  ))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  ))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  ))))))))))))))))))))))))))))))

mutual

  α : D
  α = _

  _ : f α ≡ f c
  _ = refl

_ : Set
_ = {!!}
