-- Qualified mixfix operators
module Issue597 where

open import Common.Prelude as Prel
open import Common.Level using (lzero)

lz = lzero Common.Level.⊔ lzero

module A where

  data _×_ (A B : Set) : Set where
    _,_ : A → B → A × B

  if_then_else_ : ∀ {A : Set} → Bool → A → A → A
  if true  then x else y = x
  if false then x else y = y

  pattern _+2 n = suc (suc n)

  module B where

    _₁ : ∀ {A B} → A × B → A
    (x , y)₁ = x

    _₂ : ∀ {A B} → A × B → B
    (x , y)₂ = y

    syntax Exist (λ x → p) = ∃ x ∶ p
    data Exist {A : Set}(P : A → Set) : Set where
      _,_ : (x : A) → P x → Exist P

pp : Nat → Nat
pp 0 = 0
pp 1 = 0
pp (n A.+2) = n

infix 5 add_
add_ : Nat A.× Nat → Nat
add_ p = p A.B.₁ Prel.+ p A.B.₂

six : Nat
six = add 1 A., 5

two : Nat
two = A.if true then 2 else 4

data Even : Nat → Set where
  ez  : Even 0
  ess : ∀ n → Even n → Even (suc (suc n))

pair : A.B.∃ n ∶ Even n
pair = 2 A.B., ess zero ez
