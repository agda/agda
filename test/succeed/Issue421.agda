
module Issue421 where

module Foo (_ : Set₁) where
  Id : Set → Set
  Id n = n

module FooApp = Foo Set

data ⊤ : Set where
  tt : ⊤

⟦_⟧ : ⊤ → Set → Set
⟦ tt ⟧ x = FooApp.Id x
-- works: ⟦ tt ⟧ x = Foo.Id Set x

data μ x : Set where
  fix : ⟦ x ⟧ (μ x) -> μ x
