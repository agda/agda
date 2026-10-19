
module _ where

open import Issue1839.A
open import Issue1839.B

X : DontPrintThis    -- should display as PrintThis
X = {!!}
