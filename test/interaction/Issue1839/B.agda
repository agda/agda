
module Issue1839.B where

open import Issue1839.A

postulate
  DontPrintThis : Set

{-# DISPLAY DontPrintThis = PrintThis #-}
