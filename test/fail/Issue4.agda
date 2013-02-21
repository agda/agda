-- Andreas, 2013-02-21 issue seems to have been fixed along with issue 796
-- {-# OPTIONS -v tc.decl:10 #-}
module Issue4 where

open import Common.Equality

abstract

  abstract -- a second abstract seems to have no effect

    T : Set -> Set
    T A = A

  see-through : ∀ {A} → T A ≡ A
  see-through = refl

  data Ok (A : Set) : Set where
    ok : T (Ok A) → Ok A

opaque : ∀ {A} → T A ≡ A
opaque = see-through

data Bad (A : Set) : Set where
  bad : T (Bad A) -> Bad A
