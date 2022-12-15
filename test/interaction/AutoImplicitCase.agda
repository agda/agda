
data D (A : Set) : Set where
  mkD : {x : A} → D A

getA : ∀ {A} → D A → A
getA d = {!-c!}
-- C-c C-a should produce
-- getA (mkD {x}) = x
