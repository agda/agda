-- Reported by nils.anders.danielsson, Feb 7 2014
-- The code below is accepted by Agda 2.3.2.2.

module Issue1048 where

module M (_ : Set) where

  data D : Set where
    c₁ : D
    c₂ : D → D

postulate A : Set

open M A

postulate
  ♭ : D → D
  ♯ : D → D

data S : D → Set where
  s : (d : D) → S (♭ d) → S (c₂ d)

postulate
  f : S (♭ (♯ c₁)) → S c₁

Foo : S (c₂ (♯ c₁)) → Set₁
Foo (s ._ x) with f x
... | _ = Set

-- Bug.agda:24,1-25,14
-- The constructor c₁ does not construct an element of D
-- when checking that the type (x : S (♭ (♯ c₁))) → S M.c₁ → Set₁ of
-- the generated with function is well-formed

-- Fixed.  Need to normalize constructor in checkInternal.
