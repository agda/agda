
open import Agda.Builtin.Equality
open import Agda.Builtin.List
open import Agda.Builtin.Reflection renaming (bindTC to _>>=_)
open import Agda.Builtin.Unit

macro
  pickWhatever : Term → TC ⊤
  pickWhatever hole@(meta m _) = do
    (cand ∷ _) ← getInstances m
      where [] -> typeError (strErr "No candidates!" ∷ [])
    unify hole cand
  pickWhatever _ = typeError (strErr "Already solved!" ∷ [])

-- Testing basic functionality
data YesNo : Set where instance yes no : YesNo

test₁ : YesNo
test₁ = pickWhatever

test₁-ok : test₁ ≡ yes
test₁-ok = refl

-- Testing if candidates are correctly filtered
data IsYesNo : YesNo → Set where instance
  isYes : IsYesNo yes
  isNo : IsYesNo no

test₂ : IsYesNo no
test₂ = pickWhatever

-- Testing local candidates
test₃ : {{YesNo}} → YesNo
test₃ = pickWhatever

test₃-ok : ∀ {x} → test₃ {{x}} ≡ x
test₃-ok = refl
