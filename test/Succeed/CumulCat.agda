{-# OPTIONS --cumulativity --postfix-projections #-}

open import Agda.Primitive
open import Agda.Builtin.Nat
open import Agda.Builtin.Equality

variable
  ℓ ℓ₁ ℓ₂ ℓ₃ : Level
  A B C : Set ℓ
  x y z : A
  k l m n : Nat

record Σ {ℓ} (A : Set ℓ) (B : A → Set ℓ) : Set ℓ where
  constructor _,_
  field
    fst : A
    snd : B fst
open Σ public

record Category ℓ : Set (lsuc ℓ) where
  field
    Carrier : Set ℓ
    _~>_    : Carrier → Carrier → Set ℓ
    id      : ∀ {X} → X ~> X
    _∘_     : ∀ {X Y Z} → X ~> Y → Y ~> Z → X ~> Z
open Category public

SetCat : ∀ ℓ → Category (lsuc ℓ)
SetCat ℓ .Carrier  = Set ℓ
SetCat ℓ ._~>_ A B = A → B
SetCat ℓ .id = λ x → x
SetCat ℓ ._∘_ f g = λ x → g (f x)

record Functor (c : Category ℓ₁) (c′ : Category ℓ₂) : Set (ℓ₁ ⊔ ℓ₂) where
  private
    module c  = Category c
    module c′ = Category c′

  field
    F    : c.Carrier → c′.Carrier
    fmap : {A B : c.Carrier} → A c.~> B → F A c′.~> F B
open Functor public

idFunctor : {c : Category ℓ} → Functor c c
idFunctor .F    X = X
idFunctor .fmap f = f

compFunctor : {c₁ : Category ℓ₁} {c₂ : Category ℓ₂} {c₃ : Category ℓ₃}
            → Functor c₁ c₂ → Functor c₂ c₃ → Functor c₁ c₃
compFunctor F₁ F₂ .F    X = F₂ .F (F₁ .F X)
compFunctor F₁ F₂ .fmap f = F₂ .fmap (F₁ .fmap f)

Cat : ∀ ℓ → Category (lsuc ℓ)
Cat ℓ .Carrier    = Category ℓ
Cat ℓ ._~>_ c₁ c₂ = Functor c₁ c₂
Cat ℓ .id  = idFunctor
Cat ℓ ._∘_ = compFunctor

NatTrans : {c₁ : Category ℓ₁} {c₂ : Category ℓ₂} → (F G : Functor c₁ c₂) → Set (ℓ₁ ⊔ ℓ₂)
NatTrans {c₁ = c₁} {c₂ = c₂} F G =
  let module c₁ = Category c₁
      module c₂ = Category c₂
      module F = Functor F
      module G = Functor G
  in ∀ X → F.F X c₂.~> G.F X

FunctorCat : (c₁ : Category ℓ₁) (c₂ : Category ℓ₂) → Category (ℓ₁ ⊔ ℓ₂)
FunctorCat c₁ c₂ .Carrier   = Functor c₁ c₂
FunctorCat c₁ c₂ ._~>_      = NatTrans
FunctorCat c₁ c₂ .id X      = c₂ .id
FunctorCat c₁ c₂ ._∘_ α β X =
  let module c₁ = Category c₁
      module c₂ = Category c₂
  in α X c₂.∘ β X

record Setoid ℓ : Set (lsuc ℓ) where
  field
    Carrier : Set ℓ
    _~_     : Carrier → Carrier → Set ℓ
    rfl     : ∀ {x} → x ~ x
    sym     : ∀ {x y} → x ~ y → y ~ x
    trans   : ∀ {x y z} → x ~ y → y ~ z → x ~ z
open Setoid public

DiscreteSetoid : Set ℓ → Setoid ℓ
DiscreteSetoid A .Carrier = A
DiscreteSetoid A ._~_     = _≡_
DiscreteSetoid A .rfl = refl
DiscreteSetoid A .sym refl = refl
DiscreteSetoid A .trans refl refl = refl

SetoidCat : ∀ ℓ → Category (lsuc ℓ)
SetoidCat ℓ .Carrier   = Setoid ℓ
SetoidCat ℓ ._~>_  A B =
  let module A = Setoid A
      module B = Setoid B
  in Σ {ℓ} (A.Carrier → B.Carrier)
     λ f → ∀ {x y} → x A.~ y → f x B.~ f y
SetoidCat ℓ .id  = (λ x → x) , λ x= → x=
SetoidCat ℓ ._∘_ (f , f=) (g , g=) = (λ x → g (f x)) , λ x= → g= (f= x=)

DiscreteSetoidFunctor : ∀ {ℓ} → Functor (SetCat ℓ) (SetoidCat ℓ)
DiscreteSetoidFunctor .F = DiscreteSetoid
DiscreteSetoidFunctor .fmap f .fst = f
DiscreteSetoidFunctor .fmap f .snd refl = refl

Op : Category ℓ → Category ℓ
Op c .Carrier  = c .Carrier
Op c ._~>_ A B = c ._~>_ B A
Op c .id = c .id
Op c ._∘_ = let module c = Category c in λ f g → g c.∘ f

Yoneda : {c : Category ℓ} (X : c .Carrier) → Functor c (Op (SetCat ℓ))
Yoneda {c = c} X .F Y =
  let module c = Category c
  in  Y c.~> X
Yoneda {c = c} X .fmap = c ._∘_

test : Functor (SetCat (lsuc lzero)) (Op (SetCat (lsuc (lsuc lzero))))
test = Yoneda {c = SetCat (lsuc lzero)} Set
