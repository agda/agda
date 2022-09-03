{-# OPTIONS --rewriting --confluence-check #-}

open import Agda.Primitive public

infix 4 _≣_
data _≣_
  {l : Level}
  {A : Set l}
  : -------------------------------
  {B : Set l}(x : A)(y : B) → Set l
  where
  instance refl : {x : A} → x ≣ x

{-# BUILTIN REWRITE _≣_ #-}

postulate
  𝔸   : Set

data Swap {l : Level}(A : Set l) : Set l where
  action :
    (swap : 𝔸 → 𝔸 → A → A)
    (swap-id : (a : 𝔸)(x : A) → swap a a x ≣ x)
    → -----------------------------------------
    Swap A

infix 6 _≀_
_≀_ :
  {l : Level}
  {A : Set l}
  ⦃ _ : Swap A ⦄
  (a b : 𝔸)
  → ------------
  A → A
_≀_ ⦃ action swap _ ⦄ = swap

data Swap₁
  {l m : Level}
  {A : Set l}
  ⦃ _ : Swap A ⦄
  (B : A → Set m)
  : -------------
  Set (l ⊔ m)
  where
  action₁ :
    (swap₁ :
      (a b : 𝔸)
      {x : A}
      → -----------------
      B x → B ((a ≀ b) x))
    (swap₁-id :
      (a : 𝔸)
      {x : A}
      (y : B x)
      → --------------
      swap₁ a a y ≣ y)
    → --------------------
    Swap₁ B

infix 6 _≀₁_
_≀₁_ :
  {l m : Level}
  {A : Set l}
  ⦃ _ : Swap A ⦄
  {B : A → Set m}
  ⦃ sw₁ : Swap₁ B ⦄
  (a b : 𝔸)
  {x : A}
  → -----------------
  B x → B ((a ≀ b) x)
_≀₁_ ⦃ sw₁ = action₁ swap₁ _ ⦄ = swap₁

≀₁id :
  {l m : Level}
  {A : Set l}
  ⦃ _ : Swap A ⦄
  {B : A → Set m}
  ⦃ sw₁ : Swap₁ B ⦄
  (a : 𝔸)
  {x : A}
  (y : B x)
  → ---------------
  (a ≀₁ a) y ≣ y
≀₁id ⦃ sw₁ = action₁ _ swap₁-id ⦄  = swap₁-id

{-# REWRITE ≀₁id #-}
