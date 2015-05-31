
module Issue1530.Bound {A : Set}(_<=_ : A -> A -> Set) where

data Bound : Set where
  bot : Bound
  val : A -> Bound

data LeB : Bound -> Bound -> Set where
  lebx : {b : Bound} -> LeB bot b
  lexy : {a b : A} -> a <= b -> LeB (val a) (val b)
