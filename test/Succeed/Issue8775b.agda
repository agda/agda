-- The occurs check compares a variable against the modality of the
-- position it occurs in.  For a free variable it divides the recorded
-- modality by the modality of every argument it descends into; for a
-- local binder it used to record the binder's own modality and never
-- divide it.  So a `λ` bound *inside* a `@♭` argument -- `Continuous`
-- where it is written -- was rejected as not flat enough, and no
-- metavariable whose solution has such a binder could be solved.

{-# OPTIONS --cohesion #-}

module Issue8775b where

open import Agda.Primitive

postulate
  A    : Set
  B    : A → Set
  keep : (@♭ g : A → A) → A → A

-- Inferring the parameter of `R` assigns `keep (λ a → a)`, whose binder
-- sits inside the crisp argument of `keep`.

record R (f : A → A) : Set where
  field out : A

D : Set
D = R (keep (λ a → a))

test : D → A
test r = R.out r

-- The `Π` a ♭-type carries is such a binder as well, so the same
-- failure covered every meta solved with `♭ T` for a `Π`- or `Σ`-type
-- `T`.

data ♭ {@♭ l : Level} (@♭ T : Set l) : Set l where
  con : @♭ T → ♭ T

record Box (T : Set) : Set where
  field unbox : T

E : Set
E = Box (♭ ((x : A) → B x))

test₂ : E → ♭ ((x : A) → B x)
test₂ e = Box.unbox e
