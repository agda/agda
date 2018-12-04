record R (X : Set) : Set₁ where
  field
    P : X → Set
    f : ∀ {x : X} → P x → P x

open R {{…}}

test : ∀ {X} {{r : R X}} {x : X} → P x → P x
test p = f p

-- WAS: instance search fails with several candidates left
-- SHOULD: succeed
