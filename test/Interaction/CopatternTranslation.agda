-- Record expressions are translated to copattern matches.

module _ where

record _×_ (A B : Set) : Set where
  constructor _,_
  field
    fst : A
    snd : B

open _×_

dup : ∀ {A} → A → A × A
dup x = record {fst = x; snd = x}

-- dup is translated internally to
--   dup x .fst = x
--   dup x .snd = x
-- so dup should not normalise to λ x → x , x

dup' : ∀ {A} → A → A × A
dup' x = x , x

-- But dup' is not translated, so dup' does reduce.
