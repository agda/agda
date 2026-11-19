module Issue6962Head where

-- A permissively parsed head must still start with a function name.
(bad) (A : Set) : A → A
