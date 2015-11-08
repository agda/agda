module IrrelevantLambda where

postulate
  A : Set
  P : .A -> Set

f : ._ -> Set
f = λ .x -> P x

f' = λ .(x : _) -> P x

f'' = λ .{x y z : _} -> P x

g : ((.A -> Set) -> Set) -> Set
g k = k f
