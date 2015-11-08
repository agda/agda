
open import Common.Prelude
open import Common.Reflection
open import Common.Equality

infixr 40 _∷_

data L (A : Set) : Set where
  [] : L A
  _∷_ : A → L A → L A

record R : Set where

checkType : primQNameType (quote L._∷_) ≡
  el (lit 1) (pi (arg (argInfo hidden relevant) (el (lit 1) (sort (lit 0))))
               (abs "A" (el (lit 0)
                (pi (arg (argInfo visible relevant) (el (lit 0) (var 0 [])))
                 (abs "_" (el (lit 0)
                  (pi
                   (arg (argInfo visible relevant)
                     (el (lit 0)
                      (def (quote L) (arg (argInfo visible relevant) (var 1 []) ∷ []))))
                   (abs "_" (el (lit 0)
                    (def (quote L)
                     (arg (argInfo visible relevant) (var 2 []) ∷ [])))))))))))
checkType = refl

getCons : QName → List QName
getCons d with primQNameDefinition d
... | dataDef df = primDataConstructors df
... | _          = []

checkCons : getCons (quote L) ≡ (quote L.[] ∷ quote L._∷_ ∷ [])
checkCons = refl
