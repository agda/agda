
module _ where

module M where

  infixr 3 _!_
  data D : Set₁ where
    _!_ : D → D → D

infixl 3 _!_
data E : Set₁ where
  _!_ : E → E → E

open M

postulate
  [_]E : E → Set
  [_]D : D → Set

fail : ∀ {d e} → [ (d ! d) ! d ]D → [ e ! (e ! e) ]E
fail x = x -- should use the right fixity for the overloaded constructor
