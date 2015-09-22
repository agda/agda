module UnknownImplicitInstance where

⟨⟩ : {A : Set} {{a : A}} → A
⟨⟩ {{a}} = a

postulate
  B : Set
  instance b : B
  f : {A : Set₁} {{a : A}} → A

x : Set
x = f
