
open import Agda.Builtin.Nat

data Bal : Nat → Nat → Nat → Set where
  leanR : ∀ {n} → Bal n (suc n) (suc n)
  leanL : ∀ {n} → Bal (suc n) n (suc n)

data Tree : Nat → Set where
  leaf : Tree 0
  node : ∀ {hˡ hʳ h} (t : Tree hʳ) (b : Bal hˡ hʳ h) → Tree (suc h)

join : ∀ {hˡ hʳ} h → Bal hˡ hʳ h → Tree (suc hˡ) → Nat
join _       leanL (node (node t b) leanR) = 0
join (suc _) leanL (node t          leanL) = 1
join _       leanR t₁                      = 2
