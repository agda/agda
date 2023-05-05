{-# OPTIONS --erased-cubical --erasure --no-main #-}
module Issue6530 where

open import Agda.Primitive
open import Agda.Builtin.Sigma
open import Agda.Builtin.Nat
open import Agda.Builtin.Cubical.Path

open import Agda.Primitive.Cubical public
  renaming ( primIMin       to _∧_  -- I → I → I
           ; primIMax       to _∨_  -- I → I → I
           ; primINeg       to ~_   -- I → I
           ; isOneEmpty     to empty
           ; primComp       to comp
           ; primHComp      to hcomp
           ; primTransp     to transp)

private variable
  ℓ : Level
  A : Set ℓ
  x y w z : A

refl : x ≡ x
refl {x = x} i = x

sym : x ≡ y → y ≡ x
sym p i = p (~ i)

isContr : Set ℓ → Set ℓ
isContr A = Σ A (λ x → ∀ y → x ≡ y)

isProp : Set ℓ → Set ℓ
isProp A = (x y : A) → x ≡ y

isSet : Set ℓ → Set ℓ
isSet A = (x y : A) → isProp (x ≡ y)


doubleComp-faces : {x y z w : A } (p : x ≡ y) (r : z ≡ w)
                 → (i : I) (j : I) → Partial (i ∨ ~ i) A
doubleComp-faces p r i j (i = i0) = p (~ j)
doubleComp-faces p r i j (i = i1) = r j

_∙∙_∙∙_ : w ≡ x → x ≡ y → y ≡ z → w ≡ z
(p ∙∙ q ∙∙ r) i =
  hcomp (doubleComp-faces p r i) (q i)

_∙_ : x ≡ y → y ≡ z → x ≡ z
p ∙ q = refl ∙∙ p ∙∙ q

isContr→isProp : isContr A → isProp A
isContr→isProp (x , p) a b = sym (p a) ∙ p b

isProp→isSet : isProp A → isSet A
isProp→isSet h a b p q j i =
  hcomp (λ k → λ { (i = i0) → h a a k
                 ; (i = i1) → h a b k
                 ; (j = i0) → h a (p i) k
                 ; (j = i1) → h a (q i) k }) a

isOfHLevel : Nat → Set ℓ → Set ℓ
isOfHLevel 0 A = isContr A
isOfHLevel 1 A = isProp A
isOfHLevel (suc (suc n)) A = (x y : A) → isOfHLevel (suc n) (x ≡ y)

isOfHLevelSuc : (n : Nat) → isOfHLevel n A → isOfHLevel (suc n) A
isOfHLevelSuc 0 = isContr→isProp
isOfHLevelSuc 1 = isProp→isSet
isOfHLevelSuc (suc (suc n)) h a b = isOfHLevelSuc (suc n) (h a b)
