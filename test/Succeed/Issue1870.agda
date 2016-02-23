
module _ where

postulate
  U : Set
  u : U

module M (x : U) where
  postulate f : U → U

module M₁ = M (M.f u u)  -- this caused a 'recursive display form' error
