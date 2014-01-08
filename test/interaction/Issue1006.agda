
record Σ (A : Set) (B : A → Set) : Set where
  constructor _,_
  field
    proj₁ : A
    proj₂ : B proj₁

data ⊤ : Set where tt : ⊤

id : ⊤ → ⊤
id tt = tt

data Foo : ⊤ → Set where
  foo : {x : ⊤} → Foo (id x)

test : {x : Σ ⊤ Foo} → Set
test {x₁ , x₂} = {!x₂!}
