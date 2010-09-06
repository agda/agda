-- 2010-09-06 Andreas

module IrrelevantVar where

-- type checker should fail and complain that x is irrelevant and cannot be used

f : {A : Set} -> .A -> A -> A
f x y = x
