-- {-# OPTIONS -v import.iface:10 #-}

-- Both of the following modules define the same rewrite rule,
-- but importing them both should still succeed,
-- even when opening them.

open import Nat1
open import Nat2
import Test1
import Test2
