module Issue1039 where
open import Common.Level

Test : ∀ {a b} → Set a → Set (a ⊔ b) → Set a
Test X Y = X

test : Set (lsuc lzero)
test = Test Set (Set (lsuc lzero))

test₂ : ∀ {l} → Set (lsuc l)
test₂ {l} = Test (Set l) (Set (lsuc l))

