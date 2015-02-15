{-# OPTIONS --no-sized-types #-}

open import Common.Size renaming (↑_ to _^)

data Nat : {size : Size} -> Set where
  zero : {size : Size} -> Nat {size ^}
  suc  : {size : Size} -> Nat {size} -> Nat {size ^}

weak : {i : Size} -> Nat {i} -> Nat {∞}
weak x = x

-- Should give error without sized types.

-- .i != ∞ of type Size
-- when checking that the expression x has type Nat
