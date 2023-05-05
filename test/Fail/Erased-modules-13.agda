{-# OPTIONS --erasure #-}

module _ where

module Not-erased where

  data Unit : Set where
    unit : Unit

module @0 Erased = Not-erased

-- The constructor Erased.unit is erased, but matching on this
-- constructor does not make the type-checker enter compile-time mode.

rejected : {@0 A : Set} → Erased.Unit → @0 A → A
rejected Erased.unit x = x

-- If the code above were allowed, then the following code would be
-- accepted.

bad : {@0 A : Set} → @0 A → A
bad = rejected Not-erased.unit
