{-# OPTIONS --without-K --smart-with #-}

open import Agda.Builtin.Equality
import Agda.Builtin.Equality.Rewrite

-- Example due to Jesper Cockx

data Unit : Set where ⟨⟩ : Unit

variable
  A B : Set
  x y : A

PathOver : (P : A → Set) (eq : x ≡ y) → P x → P y → Set
PathOver P refl p q = p ≡ q

hide : Unit → A → A
hide ⟨⟩ x = x

unitp : (u : Unit) → u ≡ ⟨⟩
unitp ⟨⟩ = refl

unitElim : (P : Unit → Set) → P ⟨⟩ → (u : Unit) → P u
unitElim P d ⟨⟩ = d

local-reflect : (u : Unit) (eq : hide u x ≡ x)
              → PathOver (λ v → hide v x ≡ x) (unitp u) eq refl
local-reflect {x = x} u eq
  rewrite eq rewrite unitp u = refl

uip : (eq : x ≡ x) → eq ≡ refl
uip eq = local-reflect ⟨⟩ eq
