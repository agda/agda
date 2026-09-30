-- Reported and fixed by Andrea Vezzosi.

module Issue902 where

module M (A : Set) where

postulate
  A : Set
  F : Set -> Set

test : A
test = {! let module m = M (F A) in ? !}
-- C-c C-r gives  let module m = M F A in ?
--    instead of  let module m = M (F A) in ?
