{-# OPTIONS --universe-polymorphism #-}

module LevelWithBug where

open import Common.Level

postulate
  take : ∀ a → Set a → Set
  a : Level
  A : Set a
  Goal : Set → Set
  goal : ∀ X → Goal X

-- The meta got solved by Level (Max [Plus 0 (NeutralLevel a)]) which
-- didn't match the argument in the with expression which is simply a.
-- Now the level noise should go away when it's not useful.
foo : Goal (take _ A)
foo with take a A
... | z = goal z

-- Here's another more complicated one.

data List {a}(A : Set a) : Set a where
  [] : List A
  _∷_ : A → List A → List A

data _≡_ {a}{A : Set a}(x : A) : A → Set a where
  refl : x ≡ x

{-# BUILTIN EQUALITY _≡_ #-}
{-# BUILTIN REFL refl #-}

-- Sums commute with Any (for a fixed list).

data Any {a p} {A : Set a}
         (P : A → Set p) : List A → Set (a ⊔ p) where
  there : ∀ {x xs} (pxs : Any P xs) → Any P (x ∷ xs)

amap : ∀ {a p q} {A : Set a} {P : A → Set p} → {Q : A → Set q} →
      (∀ {x} → P x → Q x) → ∀ {xs} → Any P xs → Any Q xs
amap g (there pxs) = there (amap g pxs)

data _+_ {a b} (A : Set a) (B : Set b) : Set (a ⊔ b) where
  inl : (x : A) → A + B
  inr : (y : B) → A + B

smap : ∀ {a b c d} {A : Set a} {B : Set b} {C : Set c} {D : Set d} →
      (A → C) → (B → D) → (A + B → C + D)
smap f g (inl x) = inl (f x)
smap f g (inr y) = inr (g y)

postulate
  p q : Level
  P : A → Set p
  Q : A → Set q

to : ∀ xs → Any P xs + Any Q xs → Any (λ x → P x + Q x) xs
to xs (inl pxs) = amap inl pxs
to xs (inr pxs) = amap inr pxs

from : ∀ xs → Any (λ x → P x + Q x) xs → Any P xs + Any Q xs
from ._ (there p) = smap there there (from _ p)

-- Here the abstraction didn't work because a NeutralLevel was replaced
-- by an UnreducedLevel during abstraction.
fromto : ∀ xs (p : Any P xs + Any Q xs) → from xs (to xs p) ≡ p
fromto .(x ∷ xs) (inl (there {x}{xs} p)) rewrite fromto xs (inl p) = refl
fromto .(x ∷ xs) (inr (there {x}{xs} q)) rewrite fromto xs (inr q) = refl
