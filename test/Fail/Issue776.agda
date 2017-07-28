-- Andreas, 2017-07-28, issue #776 reported by p.giarusso on 30 Dec 2012

open import Agda.Primitive

-- Note Set₁ instead of Set (suc l)
data _:=:_ {l : Level} (A : Set l) (B : Set l) : Set₁ where
  proof : {F : Set l → Set l} → F A → F B → A :=: B

-- WAS: no error message

-- Expected:
-- The type of the constructor does not fit in the sort of the
-- datatype, since Set (lsuc l) is not less or equal than Set₁
-- when checking the constructor proof in the declaration of _:=:_
