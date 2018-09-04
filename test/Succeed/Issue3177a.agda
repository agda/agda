
record _×_ (A B : Set) : Set where
  constructor _,_
  field
    fst : A
    snd : B

open _×_
infixr 1 _,_

_∩_ : {I : Set} → (I → Set) → (I → Set) → I → Set
P ∩ Q = λ i → P i × Q i

record Preorder : Set₁ where
  no-eta-equality
  field I : Set

infix 4 _∈_

postulate
  Ty World Cxt : Set
  All : (P : Ty → Set) → Cxt → Set
  _∈_ : Ty → World → Set

module Monotone (pre : Preorder) where
  open Preorder pre

  postulate
    Monotone : (I → Set) → Set

  instance
    postulate
      all-monotone : {Γ : Cxt} {C : Ty → I → Set}
                     ⦃ w : ∀ {ty} → Monotone (C ty) ⦄ →
                     Monotone (λ W → All (λ ty → C ty W) Γ)

module Monad (pre : Preorder) (let open Preorder pre)
             (M : (I → Set) → I → Set) where
  postulate
    _>>=_ : ∀ {P Q W} → M P W → (∀ {W'} → P W' → M Q W') → M Q W

postulate
  M   : (World → Set) → World → Set
  Val : World → Set

preorder : Preorder
preorder .Preorder.I = World

module Inner (Dummy : Set) where -- Succeeds if no Dummy

  private
    -- Succeeds if type is given
    pre : _ -- Preorder
    pre = preorder

  open Monotone pre
  open Monad pre M

  postulate
    R : World → Set

    instance
      any-monotone : ∀ {ty} → Monotone (ty ∈_)

    local : ∀ Γ {W} → R W × All (_∈ W) Γ → M Val W
    ^     : ∀ {Q : World → Set} ⦃ m : Monotone Q ⦄ → ∀ {W} → Q W → M (R ∩ Q) W

  eval-method : ∀ Γ {W} → All (_∈ W) Γ → M Val W
  eval-method Γ args =
    ^ args >>= local _ -- Succeeds if giving Γ for _
