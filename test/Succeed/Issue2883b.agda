
record R : Set₁ where
  field
    X : Set

data Δ (A : Set) : Set where
  _,_ : A → A → Δ A

foo : (A : Set) → R → Δ A → Set
foo A = λ { r (x , y) → let open R r in X }
  -- (y₁ : r) → Set !=< Set of type Set₁
  -- when checking that the expression .Foo.X has type Set
