-- Positivity for functions in instantiated parameterised modules.
module Issue421 where

module Foo (_ : Set₁) where
  Id : Set → Set
  Id n = n

module FooApp = Foo Set

data ⊤ : Set where
  tt : ⊤

⟦_⟧₁ : ⊤ → Set → Set
⟦ tt ⟧₁ x = FooApp.Id x
-- works: ⟦ tt ⟧ x = Foo.Id Set x

data μ₁ x : Set where
  fix : ⟦ x ⟧₁ (μ₁ x) -> μ₁ x

-- Instantiating the module in another parameterised module:

module Matrices (J : Set) where

  Id : (J → Set) → J → Set
  Id m i = m i

data Poly : Set where
  id : (D : Poly) -> Poly

module Dim (I : Set) where
  module M = Matrices I

  ⟦_⟧₂ : Poly → (I → Set) → (I → Set)
  ⟦ id D ⟧₂ x i = M.Id x i
  
  data μ₂ (p : Poly) (i : I) : Set where
    fix : ⟦ p ⟧₂ (μ₂ p) i -> μ₂ p i
