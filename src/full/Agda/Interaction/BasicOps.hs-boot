module Agda.Interaction.BasicOps where

data OutputForm a b
data OutputConstraint a b
data OutputConstraint' a b

data UseForce
instance Show UseForce
instance Read UseForce

data ComputeMode
instance Show ComputeMode
instance Read ComputeMode

data Rewrite
instance Show Rewrite
instance Read Rewrite
