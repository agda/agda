-- data construction, disproving

module Auto-DataConstruction where

open import Auto.Prelude


module Disproving where

 h0 : {X : Set} → (xs ys : List X) → (xs ++ ys) ≡ (ys ++ xs)
 h0 = {!-d Fin!}
