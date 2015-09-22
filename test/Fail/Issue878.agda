module Issue878 where

data _==_ {A : Set} (a : A) : A → Set where
  idp : a == a

data ⊤ : Set where
  tt : ⊤

record args : Set₁ where
  field
    P : ⊤ → Set
    g : (b : ⊤) → P b

module _ (r : args) where
  open args r

  postulate
    ext : ∀ b → P b

module _ {r : args} where
  open args r

  postulate
    β-r : ∀ b → ext r b == g b

a : args
a = record {P = λ x → (⊤ → ⊤); g = λ x → λ c → tt}

err : ext a tt tt == tt
err = β-r tt
-- WAS: __IMPOSSIBLE__ in Conversion.hs
