{-# OPTIONS --cubical-compatible --erased-quotients #-}

open import Agda.Builtin.Bool
open import Agda.Builtin.Equality
open import Agda.Builtin.Erased.Quotient
open import Agda.Builtin.IO
open import Agda.Builtin.String renaming (primStringAppend to _++_)
open import Agda.Builtin.Unit
open import Agda.Primitive

private variable
  a b r : Level
  A B   : Set _
  @0 R  : A → A → Set _
  x y z : A

postulate
  putStrLn      : String → IO ⊤
  @0 String-set : Is-set String

{-# FOREIGN GHC import qualified Data.Text.IO as Text #-}
{-# COMPILE GHC putStrLn = Text.putStrLn #-}
{-# COMPILE JS putStrLn = x => y => (console.log(x), y) #-}

trans : x ≡ y → y ≡ z → x ≡ z
trans refl refl = refl

subst-const : {eq : x ≡ y} → subst (λ _ → A) eq z ≡ z
subst-const {eq = refl} = refl

qrec' :
  (f : A → B) →
  @0 (∀ {x y} → R x y → f x ≡ f y) →
  @0 Is-set B →
  A / R → B
qrec' f resp set =
  qrec _ f (λ r → trans subst-const (resp r)) (λ _ → set)

main : IO ⊤
main =
  putStrLn
    (qrec'
       {R = _≡_}
       (λ where
          true  → "OK"
          false → "Failure")
       (λ @0 { refl → refl })
       String-set
       [ true ])
