-- Andreas, 2013-11-08
module Issue532 where

module M (A : Set) where
  postulate
    ax : A
    P  : A → Set

record R (A : Set) : Set where
  open M A public
  field
    f : P ax
open R

-- Error WAS:
-- Not a valid let-declaration
-- when scope checking let open M A public in (f : P ax) → Set₀

S : {A : Set} → R A → Set
S r = P r (ax r)

-- Works now.
