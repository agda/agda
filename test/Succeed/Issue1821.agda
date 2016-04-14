-- Andreas, 2016-04-14 Issue 1821
-- pts rule for SizeUniv not implemented properly

open import Common.Size
open import Common.Equality

record Reveal_·_is_  {A : Set} {B : A → Set}
                    (f : (x : A) → B x) (x : A) (y : B x) :
                    Set where
  constructor [_]
  field eq : f x ≡ y

inspect : ∀ {A : Set} {B : A → Set}
          (f : (x : A) → B x) (x : A) → Reveal f · x is f x
inspect f x = [ refl ]

record Co i : Set where
  coinductive
  field force : ∀{j : Size< i} → Co j

test : ∀ (n : Co ∞) → Set
(test n) with inspect Co.force n
(test n) | n' = Co ∞

-- Error WAS:
-- SizeUniv != Set
-- when checking that the type
-- ...
-- of the generated with function is well-formed
