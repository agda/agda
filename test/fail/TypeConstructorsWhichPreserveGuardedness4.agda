{-# OPTIONS --guardedness-preserving-type-constructors #-}

module TypeConstructorsWhichPreserveGuardedness4 where

codata ∞ (A : Set₁) : Set₁ where
  ♯_ : A → ∞ A

♭ : {A : Set₁} → ∞ A → A
♭ (♯ x) = x

data Rec (A : ∞ Set) : Set where
  fold : ♭ A → Rec A

D : Set
D = Rec (♯ (D → D))

_·_ : D → D → D
fold f · x = f x

ω : D
ω = fold (λ x → x · x)

Ω : D
Ω = ω · ω
