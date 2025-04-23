{-# OPTIONS --safe --cubical #-}
module Issue7668 where

open import Agda.Builtin.Cubical.Path
open import Agda.Primitive.Cubical
open import Agda.Builtin.Bool

import Agda.Builtin.Equality as I

data ⊥ : Set where

cong : {A B : Set} (f : A → B) {x y : A} → x ≡ y → f x ≡ f y
cong f p i = f (p i)

false≢true : false ≡ true → ⊥
false≢true p = primTransp (λ i → F (p i)) i0 false
  where
  F : Bool → Set
  F false = Bool
  F true = ⊥

pathToId : {A : Set} {x y : A} → x ≡ y → x I.≡ y
pathToId {x = x} p = primTransp (λ i → x I.≡ p i) i0 I.refl

idToPath : {A : Set} {x y : A} → x I.≡ y → x ≡ y
idToPath {x = x} I.refl i = x

-- Used to be: the inductive identity type had an 'unused' polarity for
-- the type argument, so the occurrence of 'Bad' in the type of seg was
-- ignored.

data Bad : Set where
  zero : Bad
  one : Bad
  seg : (zero I.≡ one → false ≡ true) → zero ≡ one

bad : Bad → Bool
bad zero = false
bad one = true
bad (seg f i) = f (pathToId (seg f)) i

oops : ⊥
oops = false≢true (cong bad (seg λ e → cong bad (idToPath e)))
