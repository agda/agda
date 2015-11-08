
-- Eta contraction didn't consider hiding when contracting,
-- leading to the following module not type checking.
module Issue259 where

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
