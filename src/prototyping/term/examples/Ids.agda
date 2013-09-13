module Ids where

id : {A : Set} -> A -> A
id x = x

slow : {A : Set} -> A -> A
slow = id id id id id id id id id id id id id id id id id id

-- The example above is based on one in "Implementing Typed
-- Intermediate Languages" by Shao, League and Monnier.
