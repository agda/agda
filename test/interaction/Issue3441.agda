open import Agda.Primitive

f : ∀ {a b c} → Set a → Set b → Set c → Set {!!} -- WAS solution: (a ⊔ (b ⊔ c))
f A B C = A → B → C                              -- NOW:          (a ⊔ b ⊔ c)
