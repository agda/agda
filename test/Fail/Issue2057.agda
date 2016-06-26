
record R (A : Set) : Set₁ where
  field
    P : A → Set
    p : (x : A) → P x

module M (r : (A : Set) → R A) where

  open module R′ {A : Set} = R (r A) public

postulate
  r : (A : Set) → R A
  A : Set

open M r

internal-error : (x : A) → P x
internal-error x = p
