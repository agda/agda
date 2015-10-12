
module _ where

open import Common.Bool

private
  unused = true
  used = true

private
 module Private where
  not-in-scope = true

in-scope = used
