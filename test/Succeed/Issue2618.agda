
open import Agda.Builtin.List
open import Agda.Builtin.Reflection renaming (bindTC to _>>=_)
open import Agda.Builtin.Bool
open import Agda.Builtin.Equality
open import Agda.Builtin.Nat
open import Agda.Builtin.Sigma

data Unit : Set where
  unit : Unit

data Empty : Set where

qq : ∀ {a} {A : Set a} → A → Term → TC _
qq t hole = withNormalisation true do
  `t ← quoteTC t
  ``t ← quoteTC `t
  unify hole ``t

macro

  qU  = qq {A = Unit → Set → Set}
  qE  = qq {A = Empty → Set → Set}
  qA  = qq {A = Set → Set}

case_of_ : ∀ {a b} {A : Set a} {B : Set b} → A → (A → B) → B
case x of f = f x

pattern vArg x = arg (arg-info visible relevant) x
pattern [_] x = x ∷ []

map : {A B : Set} → (A → B) → List A → List B
map f [] = []
map f (x ∷ xs) = f x ∷ map f xs

mkArgs : List Nat → List (Arg Term)
mkArgs = map λ i → vArg (var i [])

unit,X=>_∙_ : Nat → List Nat → Term
unit,X=> n ∙ args =
  pat-lam [ clause [ "X" , vArg (agda-sort (lit 0)) ]
                   (vArg (con (quote unit) []) ∷ vArg (var 0) ∷ [])
                   (var n []) ]
          (mkArgs args)

abs,X=>∙_ : List Nat → Term
abs,X=>∙ is = pat-lam [ absurd-clause ( ("()" , vArg (def (quote Empty) [])) ∷  ("X" , vArg (agda-sort (lit 0))) ∷ [])
                                      (vArg absurd ∷ vArg (var 0) ∷ []) ]
                      (mkArgs is)

abs=>∙_ : List Nat → Term
abs=>∙ is = pat-lam [ absurd-clause [ "()" , vArg (def (quote Empty) []) ] (vArg absurd ∷ []) ]
                    (mkArgs is)

_ : qU (λ { unit X → X }) ≡ unit,X=> 0 ∙ []
_ = refl

_ : (B : Set) → qU (λ { unit X → B }) ≡ unit,X=> 1 ∙ []
_ = λ _ → refl

_ : qE (λ { () X }) ≡ abs,X=>∙ []
_ = refl

_ : (B : Set) → qE (λ { () X }) ≡ abs,X=>∙ []
_ = λ _ → refl

_ : (u : Unit) → qA (case u of λ { unit X → X }) ≡ (unit,X=> 0 ∙ [ 0 ])
_ = λ _ → refl

_ : (B : Set) (u : Unit) → qA (case u of λ { unit X → B }) ≡ unit,X=> 2 ∙ [ 0 ]
_ = λ _ _ → refl

_ : (B : Set) (e : Empty) → qA (case e of λ { () X }) ≡ abs,X=>∙ [ 0 ]
_ = λ _ _ → refl

_ : qE (λ ()) ≡ abs=>∙ []
_ = refl

_ : (B : Set) → qE (λ ()) ≡ abs=>∙ []
_ = λ _ → refl

_ : (B : Set) (e : Empty) → qA (case e of λ ()) ≡ abs=>∙ [ 0 ]
_ = λ _ _ → refl

module _ (A : Set) where

  _ : qU (λ { unit X → X }) ≡ unit,X=> 0 ∙ []
  _ = refl

  _ : (B : Set) → qU (λ { unit X → B }) ≡ unit,X=> 1 ∙ []
  _ = λ _ → refl

  _ : qE (λ { () X }) ≡ abs,X=>∙ []
  _ = refl

  _ : (u : Unit) → qA (case u of λ { unit X → X }) ≡ (unit,X=> 0 ∙ [ 0 ])
  _ = λ _ → refl

  _ : (B : Set) (u : Unit) → qA (case u of λ { unit X → B }) ≡ unit,X=> 2 ∙ [ 0 ]
  _ = λ _ _ → refl

  _ : (B : Set) (e : Empty) → qA (case e of λ { () X }) ≡ abs,X=>∙ [ 0 ]
  _ = λ _ _ → refl

  _ : qE (λ ()) ≡ abs=>∙ []
  _ = refl

  _ : (B : Set) → qE (λ ()) ≡ abs=>∙ []
  _ = λ _ → refl

  _ : (B : Set) (e : Empty) → qA (case e of λ ()) ≡ abs=>∙ [ 0 ]
  _ = λ _ _ → refl
