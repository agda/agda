-- Andreas, 2014-12-02, issue reported by Jesper Cockx

open import Common.Equality

mutual
  Type : Set
  postulate
    type : Type
    Term : Type → Set

  Type = Term type

  weakenType : Type → Type → Type
  weaken : (ty ty' : Type) → Term ty → Term (weakenType ty' ty)

  weakenType ty ty' = subst Term {!!} (weaken type {!!} ty)
  weaken ty ty' t = {!!}

data Test : Type → Set where
  test : Test (weakenType type type)

-- Checking the constructor declaration was looping
-- should work now.
