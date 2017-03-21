module Fold where

open import Prelude

myfold : {ac b : Set} -> (ac -> b -> ac) -> ac -> List b -> ac
#ifdef strict
myfold = foldl!
#else
myfold = foldl
#endif

