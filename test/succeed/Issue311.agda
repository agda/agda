{-# OPTIONS --universe-polymorphism #-}

module Issue311 where

open import Common.Level

postulate
  A : Set
  C : (b : Level) (B : A → Set b) → Set b
  f : (b : Level) (B : A → Set b) → C b B → A
  g : (b : Level) (B : A → Set b) (d : C b B) → B (f b B d)
  P : (c : Level) → Set c
  Q : A → Set
  checkQ : ∀ a → Q a → Set

T : (c : Level) → Set c
T c = P c → A

Foo : (c : Level) (d : C c (λ _ → T c)) →
      Q (f c (λ _ → T c) d) → Set
Foo c d q with f c (λ _ → T c) d | g c (λ _ → T c) d
Foo c d q | x | y  = checkQ x q

-- C-c C-, gives:
--
-- Goal: Set₁
-- ————————————————————————————————————————————————————————————
-- q : Q (f c (λ _ → P c → A) d)
-- y : P c → A
-- x : A
-- d : C c (λ _ → P c → A)
-- c : Level
--
-- Note that q has type Q (f c (λ _ → P c → A) d); it should have type
-- Q x.
