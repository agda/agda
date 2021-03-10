
postulate
  admit : ∀ {i} {X : Set i} → X
  X Y Z : Set

data Id (z : Z) : Z → Set where
  refl : Id z z

record Square : Set₁ where
  field
    U : Set
    u : U
open Square

record RX : Set where
  field x : X
open RX

record R : Set where
  -- This definition isn't used; without it,
  -- the internal error disappears.
  r : Square
  r .U = admit
  r .u = admit

  module M (z₀ z₁ : Z) where
    f : Id z₀ z₁ → RX
    f refl = {!λ where .x → ?!}
