import Issue6931.One as One

module Issue6931.Two (A : Set)
  (let module M = One A)
  (x : M.B) where

  -- must be empty
