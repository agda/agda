-- Andreas, 2016-05-19, issue 1986, after report from Nisse
-- Andreas, 2016-06-02 fixed
-- This has been reported before as issue 842

-- {-# OPTIONS -v tc.cover:20 #-}
-- {-# OPTIONS -v tc.cc:20 -v reduce.compiled:100 #-}

open import Common.Equality

data Bool : Set where
  true false : Bool

not : Bool → Bool
not true = false
not      = λ _ → true

not-true : not true ≡ false
not-true = refl

not-false : not false ≡ true
not-false = refl

record _×_ (A B : Set) : Set where
  constructor _,_
  field fst : A
        snd : B
open _×_

dup : ∀{A : Set}(a : A) → A × A
fst (dup a) = a
dup a =  a , a

fst-dup : ∀{A} (a : A) → fst (dup a) ≡ a
fst-dup a = refl

snd-dup : ∀{A} (a : A) → snd (dup a) ≡ a
snd-dup a = refl
