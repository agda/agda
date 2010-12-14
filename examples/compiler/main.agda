module main where

open import Not-named-according-to-the-Haskell-lexical-syntax

main = return Not-named-according-to-the-Haskell-lexical-syntax.unit

-- The following code once triggered an MAlonzo bug resulting in the
-- error message "Panic: ... no such name main.M.d".

module M where
  data D : Set where
    d : D
