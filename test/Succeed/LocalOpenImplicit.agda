module LocalOpenImplicit where

record Id (a : Set) : Set where
  field id : a -> a

foo : {a b : Set} -> Id a -> Id b -> (a -> b) -> a -> b
foo id1 id2 f x = id id2 (f (id id1 x))
  where open Id

