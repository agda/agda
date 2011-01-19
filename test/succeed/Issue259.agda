module Issue259 where

-- Eta contraction didn't consider hiding when contracting,
-- leading to the following module not type checking.

module A where

  postulate
    A    : Set
    B    : A → Set
    foo  : (∀ x → B x) → A
    q    : ∀ {x} → B x
    foo′ : (∀ {x} → B x) → A

  bar : A
  bar = foo (λ y → q {y})

  Baz : B bar → Set → Set
  Baz b C with C
  Baz b C | _ = C

  -- In fact you're not allowed to eta contract hidden lambdas at all.
  bar′ : A
  bar′ = foo′ (λ {y} → q {y})

  Baz′ : B bar′ → Set → Set
  Baz′ b C with C
  Baz′ b C | _ = C

-- After eta-contraction was turned off the following code was also
-- accepted.

module B where

  postulate
    A : Set
    a : A
    b : ({x : A} → A) → A
    C : A → Set

  d : {x : A} → A
  d {x} = a

  e : A
  e = b (λ {x} → d {x})

  F : C e → Set₁
  F _ with Set
  F _ | _ = Set
