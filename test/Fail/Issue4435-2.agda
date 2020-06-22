module Issue4435-2 where

record ⊤ : Set where

data Foo (a : Set) : Set where
Bar : {a : Set} → Foo a → Set

-- Here, the error message does NOT include
-- "Perhaps you meant to write 'data Foo a where'"
-- because Foo is defined above (rather than declared - note the "where"
-- compared to Issue4435-1.agda).
data Foo a : Set where
  c1 : Foo a
  c2 : (x : Foo a) (y : Bar x → Foo a) → Foo a

Bar c1 = ⊤
Bar (c2 a b) = (x : Bar a) → Bar (b x)
