
open import Common.Prelude hiding (_>>=_)
open import Common.Reflection
open import Common.TC
open import Common.Equality

infixr 1 _>>=_
_>>=_ = bindTC

record Functor (F : Set → Set) : Set₁ where
  field
    fmap : ∀ {A B} → (A → B) → F A → F B

IdF : Functor (λ A → A)
unquoteDef IdF =
  defineFun IdF (clause (vArg (projP (quote Functor.fmap)) ∷ vArg (var "f") ∷ vArg (var "x") ∷ [])
                        (var 1 (vArg (var 0 []) ∷ [])) ∷ [])

check : ∀ {A B} (f : A → B) (x : A) → Functor.fmap IdF f x ≡ f x
check f x = refl

open Functor {{...}}

instance
  InstF : Functor (λ A → A)
  unquoteDef InstF =
    defineFun InstF (clause (iArg (projP (quote fmap)) ∷ vArg (var "f") ∷ vArg (var "x") ∷ [])
                            (var 1 (vArg (var 0 []) ∷ [])) ∷ [])

check₁ : ∀ {A B} (f : A → B) (x : A) → fmap f x ≡ f x
check₁ f x = refl

