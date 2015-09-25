-- Andreas, 2011-10-04, transcription of Dan Doel's post on the Agda list
{-# OPTIONS --experimental-irrelevance #-}
module IrrelevantMatchRefl where

import Common.Level
open import Common.Equality hiding (subst)

-- irrelevant subst should be rejected, because it suggests
-- that the equality proof is irrelevant also for reduction
subst : ∀ {i j}{A : Set i}(P : A → Set j){a b : A} → .(a ≡ b) → P a → P b
subst P refl x = x

postulate
  D   : Set
  lie : (D → D) ≡ D

-- the following two substs may not reduce! ...
abs : (D → D) → D
abs f = subst (λ T → T) lie f

app : D → D → D
app d = subst (λ T → T) (sym lie) d

ω : D
ω = abs (λ d → app d d)

-- ... otherwise Ω loops
Ω : D
Ω = app ω ω

-- ... and this would be a real fixed-point combinator
Y : (D → D) → D
Y f = app δ δ
  where δ = abs (λ x → f (app x x))

K : D → D
K x = abs (λ y → x)

K∞ : D
K∞ = Y K

mayloop : K∞ ≡ abs (λ y → K∞)
mayloop = refl
-- gives error D != D → D
