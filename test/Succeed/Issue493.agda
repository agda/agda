
module Issue493 where

module M where
  postulate A B C : Set

module M₁ = M renaming (B to Y) hiding (A)
module M₂ = M using (A) using (B)
module M₃ = M hiding (A) hiding (B)

open M using (A) public
