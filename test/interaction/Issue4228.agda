postulate
  F : Set → Set
  P : (A : Set) → F A → Set
  f : (A : Set) → F A

variable
  A : Set

postulate
  p : P {!!} (f A)   -- C-c C-,



-- Goal: Set
-- ————————————————————————————————————————————————————————————
-- genTel : Issue3656.GeneralizeTel   (not in scope)
