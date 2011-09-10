-- This is mainly a test of the quality of error messages for
-- termination problems.

module TerminationLambda where

postulate Id : Set → Set

F : Set → Set
F = λ A → F (Id A)
