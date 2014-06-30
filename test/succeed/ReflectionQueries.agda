
open import Common.Prelude
open import Common.Reflect
open import Common.Equality

data L (A : Set) : Set where
  [] : L A
  _∷_ : A → L A → L A

record R : Set where

checkType : primQNameType (quote L._∷_) ≡
  el (lit 1) (pi (arg (arginfo hidden relevant) (el (lit 1) (sort (lit 0))))
               (el (lit 0)
                (pi (arg (arginfo visible relevant) (el (lit 0) (var 0 [])))
                 (el (lit 0)
                  (pi
                   (arg (arginfo visible relevant)
                    (el (lit 0)
                     (def (quote L) (arg (arginfo visible relevant) (var 1 []) ∷ []))))
                   (el (lit 0)
                    (def (quote L)
                     (arg (arginfo visible relevant) (var 2 []) ∷ []))))))))
checkType = refl

getCons : QName → List QName
getCons d with primQNameDefinition d
... | dataDef df = primDataConstructors df
... | _          = []

checkCons : getCons (quote L) ≡ (quote L.[] ∷ quote L._∷_ ∷ [])
checkCons = refl
