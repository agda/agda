-- Andreas, 2011-10-04
-- I'd like to infer the type of a even though it is irrelevant
-- E.g. when pressing C-c C-.
module InferIrrelevant where

f : (A : Set)(g : .A → A).(a : A) → A
f A g a = {!a!}