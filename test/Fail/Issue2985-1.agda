open import Agda.Builtin.Size

mutual

  data Unit (i : Size) : Set where
    c : Unit′ i → Unit i

  record Unit′ (i : Size) : Set where
    coinductive
    field
      force : {j : Size< i} → Unit j

open Unit′ public

tail : Unit ∞ → Unit ∞
tail (c x) = force x

u : (∀ {i} → Unit′ i → Unit i) →
    ∀ {i} → Unit i
u cons = tail (cons λ { .force → u cons })

bad : Unit ∞
bad = u c
