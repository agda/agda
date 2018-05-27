-- Andreas, 2016-01-18, Issue1778, reported by mechvel
-- record pattern elimination must preserve hiding information

-- {-# OPTIONS --show-implicit #-}

open import Common.Prelude using (⊤)
open import Common.Equality
open import Common.Product
-- assuming _×_ is a record type (not data type)

module _ (A : Set) (let T = ⊤ → {p : A × A} → A) (f : T) where

swap : T → T
swap f _ {x , y} = f _ {y , x}
-- becomes by record pattern elimination
-- WAS: swap f _ xy   = f _ {proj₂ xy , proj₁ xy}
-- NOW: swap f _ {xy} = f _ {proj₂ xy , proj₁ xy}

test : f ≡ swap (swap f)
test with Set₂ -- trigers internal checking of type
test | _ = refl

-- WAS:
-- Expected a hidden argument, but found a visible argument
-- when checking that the type
-- (w : Set₁) → f ≡ (λ _ xy → f (record {}))
-- of the generated with function is well-formed

-- NOW:
-- should succeed
