
open import Agda.Primitive

record Functor {a b} (F : Set a → Set b) : Set (lsuc a ⊔ b) where
  field
    fmap : ∀ {A B} → (A → B) → F A → F B

open Functor {{...}} public

module _ {a b} (F : Set a → Set b) where
  record FunctorZero : Set (lsuc a ⊔ b) where
    field
      empty : ∀ {A} → F A
      overlap {{super}} : Functor F

  record Alternative : Set (lsuc a ⊔ b) where
    infixl 3 _<|>_
    field
      _<|>_ : ∀ {A} → F A → F A → F A
      overlap {{super}} : FunctorZero

open FunctorZero {{...}} public

open Alternative {{...}} public

record StateT {a} (S : Set a) (M : Set a → Set a) (A : Set a) : Set a where
  no-eta-equality
  constructor stateT
  field runStateT : S → M A

open StateT public

module _ {a} {S : Set a} {M : Set a → Set a} where

  instance
    FunctorStateT : {{_ : Functor M}} → Functor {a = a} (StateT S M)
    runStateT (fmap {{FunctorStateT}} f m) s = fmap f (runStateT m s)

    FunctorZeroStateT : {{_ : FunctorZero M}} → FunctorZero {a = a} (StateT S M)
    runStateT (empty {{FunctorZeroStateT}}) s = empty

    AlternativeStateT : {{_ : Alternative M}} → Alternative {a = a} (StateT S M)
    runStateT (_<|>_ {{AlternativeStateT}} x y) s = runStateT x s <|> runStateT y s

--- Example with some module parameter instantiations

open import Agda.Builtin.Nat
open import Agda.Builtin.Unit

data Vec (A : Set) : Nat → Set where
  []  : Vec A 0
  _∷_ : ∀ {n} → A → Vec A n → Vec A (suc n)

postulate
  C₁ : Set → Set

record C₂ (A : Set) : Set where
  field
    f : A → A
    overlap {{super}} : C₁ A

open C₂ {{...}}

postulate
  T : (A : Set) → A → Set

module M (A : Set) (n : Nat) (xs : Vec A n) where

  unpackT : Vec A n → Set
  unpackT (x ∷ xs) = C₂ (T A x)
  unpackT [] = ⊤

  postulate instance C₁T : ∀ {x} {{C₁A : C₁ A}} → C₁ (T A x)

  C₂T : {{C₂A : C₂ A}} (ys : Vec A n) → unpackT ys
  C₂T [] = _
  f {{C₂T (y ∷ ys)}} x = x
