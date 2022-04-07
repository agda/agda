{-# OPTIONS --cubical-compatible #-}
{-# OPTIONS --allow-unsolved-metas #-}

-- This issue demonstrates that a failing termination check,
-- subsequently blocking reductions, makes some `impossible'
-- cases possible in the conversion checker.

module Issue921 where

infix 3 _==_
postulate
  _==_ : {A : Set} → A → A → Set
  transport : {A : Set} (B : A → Set) {x y : A} (p : x == y) → (B x → B y)
  ! : {A : Set} {x y : A} → (x == y → y == x)

infixr 1 _,_
record Σ (A : Set) (B : A → Set) : Set where
  constructor _,_
  field
    fst : A
    snd : B fst
open Σ public

infix 4 _≃_

_≃_ : ∀ (A : Set) (B : Set) → Set
A ≃ B = Σ (A → B) (λ _ → B → A)

postulate
  <– : {A : Set} {B : Set} → (A ≃ B) → B → A

infixr 4 _∘e_
_∘e_ : {A : Set} {B : Set} {C : Set} → B ≃ C → A ≃ B → A ≃ C
e1 ∘e e2 = ({!!} , λ c → snd e2 (snd e1 c))

module _ {A : Set} {B : A → Set} {C : (a : A) → B a → Set} where
  Σ-assoc : Σ (Σ A B) (λ z → C (fst z) (snd z)) ≃ Σ A (λ a → Σ (B a) (C a))
  Σ-assoc = ({!!} , λ {(a , (b , c)) → ((a , b) , c)})

data Ctx : Set

postulate
  Ty : Ctx → Set

data Ctx where
  _·_ : (Γ : Ctx) → Ty {!!} → Ctx

infix 5 _ctx-⇛_
_ctx-⇛_ : Ctx → Ctx → Set

-- swap these two lines and the internal error disappears
Tm : Σ Ctx Ty → Set
Γ ctx-⇛ (Δ · A) = Σ {!!} {!!}

infix 10 _*_

postulate
  _*_  : {Γ Δ : Ctx} (m : Γ ctx-⇛ Δ) → Ty {!!} → Ty {!!}

pullback : {Γ Δ : Ctx} {A : Ty Δ} → Tm (Δ , A) → (m : Γ ctx-⇛ Δ) → Tm (Γ , m * A)

infix 7 _·_
data Xtc (Γ : Ctx) : Set where
  _·_ : (A : Ty {!!}) → Xtc {!!} → Xtc Γ

infix 6 _⋯_
_⋯_ : (Γ : Ctx) → Xtc Γ → Ctx
Γ ⋯ (A · s) = (Γ · A) ⋯ s

module xtc where
  infix 5 _⇛_∣_
  _⇛_∣_ : (Γ : Ctx) {Δ : Ctx} (m : Γ ctx-⇛ Δ) → Xtc Δ → Set
  Γ ⇛ m ∣ A · T = Σ (Tm (Γ , m * A)) (λ t → Γ ⇛ (m , t) ∣ T)

  infix 5 _⇛_
  _⇛_ : (Γ : Ctx) → Σ Ctx (λ Δ → Xtc Δ) → Set
  Γ ⇛ (Δ , T) = Σ (Γ ctx-⇛ Δ) (λ m → Γ ⇛ m ∣ T)

  eq : {Γ Δ : Ctx} {T : Xtc Δ} → Γ ctx-⇛ Δ ⋯ T ≃ Γ ⇛ (Δ , T)
  eq {T = A · T} = Σ-assoc ∘e eq


weaken : (Γ : Ctx) {T : Xtc Γ} → Γ ⋯ T ctx-⇛ Γ

infix 10 _○_

_○_ : {Γ Δ Θ : Ctx} → Δ ctx-⇛ Θ → Γ ctx-⇛ Δ → Γ ctx-⇛ Θ

postulate
  _○=_ : {Γ Δ Θ : Ctx} (n : Δ ctx-⇛ Θ) (m : Γ ctx-⇛ {!!}) {A : Ty {!!}} → (n ○ m) * A == m * (n * A)

Tm P = Σ Ctx λ Γ → Σ (Ty {!!}) λ A → Σ (Xtc (Γ · A)) λ T → (Γ · A ⋯ T , weaken Γ {A · T} * A) == P

weaken (Γ · A) {T} = (weaken Γ {A · T} , (Γ , A , T , {!!}))

_○_ {Θ = Θ · _} (n , x) m = (n ○ m , transport (λ z → Tm (_ , z)) (! (n ○= m)) (pullback x m))

weaken-○-scope : {Γ Δ : Ctx} {T : Xtc Δ} (ms : Γ xtc.⇛ (Δ , T)) → weaken Δ {T} ○ snd xtc.eq ms == fst ms

pullback-var : {Γ Δ : Ctx} {A : Ty {!!}} {T : Xtc (Δ · A)}
               (ms : Γ xtc.⇛ (Δ , A · T))
             → Tm (Γ , snd xtc.eq ms * (weaken Δ {A · T} * A))
pullback-var {Γ} {Δ} {A} {T} ms =
  transport (λ z → Tm (Γ , z)) (weaken Δ {A · T} ○= snd xtc.eq ms)
    (transport (λ z → Tm (Γ , z * A)) (! (weaken-○-scope ms))
      (fst (snd ms)))

pullback (Δ' , _ , T , p) = transport (λ P → (m : _ ctx-⇛ fst P) → Tm (_ , m * snd P)) p (<– {!!} pullback-var)

weaken-○-scope {Γ} {Δ · A} {T} ((m , t) , ts) = {!!} where
  helper3 : transport (λ z → Tm (Γ , z))
                      (! (fst (weaken (Δ · A)) ○= snd xtc.eq ((m , t) , ts)))
                      (pullback-var {!!})
         == transport (λ z → Tm (Γ , z * A))
                      (! (weaken-○-scope (m , t , ts)))
                      t
  helper3 = {!!}
