open import Agda.Builtin.Bool

postulate
  F :
    Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ →
    Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ →
    Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ →
    Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ →
    Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ →
    Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ →
    Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ →
    Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ →
    Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ →
    Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ →
    Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ →
    Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ →
    Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ →
    Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ →
    Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ →
    Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ →
    Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ →
    Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ →
    Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ →
    Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ →
    Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ →
    Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ →
    Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ →
    Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ →
    Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ →
    Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ →
    Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ →
    Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ →
    Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ →
    Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ →
    Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ →
    Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ →
    Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ →
    Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ →
    Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ →
    Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ →
    Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ →
    Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ →
    Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ →
    Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ →
    Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ →
    Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ →
    Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ →
    Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ →
    Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ →
    Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ →
    Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ →
    Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ →
    Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ →
    Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ →
    Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ →
    Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ →
    Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ →
    Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ →
    Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ →
    Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ →
    Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ →
    Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ →
    Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ →
    Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ →
    Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ →
    Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ →
    Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ →
    Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ →
    Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ →
    Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ →
    Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ →
    Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ →
    Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ →
    Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ →
    Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ →
    Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ →
    Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ →
    Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ →
    Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ →
    Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ →
    Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ →
    Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ →
    Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ →
    Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ →
    Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ →
    Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ →
    Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ →
    Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ →
    Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ →
    Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ →
    Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ →
    Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ →
    Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ →
    Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ →
    Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ →
    Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ →
    Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ →
    Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ →
    Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ →
    Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ →
    Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ →
    Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ →
    Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ →
    Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ → Set₁ →
    Bool

-- The isRigid test in checkArgumentsE' does (at the time of writing)
-- treat data types as rigid.

_ = F
  Set Set Set Set Set Set Set Set Set Set
  Set Set Set Set Set Set Set Set Set Set
  Set Set Set Set Set Set Set Set Set Set
  Set Set Set Set Set Set Set Set Set Set
  Set Set Set Set Set Set Set Set Set Set
  Set Set Set Set Set Set Set Set Set Set
  Set Set Set Set Set Set Set Set Set Set
  Set Set Set Set Set Set Set Set Set Set
  Set Set Set Set Set Set Set Set Set Set
  Set Set Set Set Set Set Set Set Set Set
  Set Set Set Set Set Set Set Set Set Set
  Set Set Set Set Set Set Set Set Set Set
  Set Set Set Set Set Set Set Set Set Set
  Set Set Set Set Set Set Set Set Set Set
  Set Set Set Set Set Set Set Set Set Set
  Set Set Set Set Set Set Set Set Set Set
  Set Set Set Set Set Set Set Set Set Set
  Set Set Set Set Set Set Set Set Set Set
  Set Set Set Set Set Set Set Set Set Set
  Set Set Set Set Set Set Set Set Set Set
  Set Set Set Set Set Set Set Set Set Set
  Set Set Set Set Set Set Set Set Set Set
  Set Set Set Set Set Set Set Set Set Set
  Set Set Set Set Set Set Set Set Set Set
  Set Set Set Set Set Set Set Set Set Set
  Set Set Set Set Set Set Set Set Set Set
  Set Set Set Set Set Set Set Set Set Set
  Set Set Set Set Set Set Set Set Set Set
  Set Set Set Set Set Set Set Set Set Set
  Set Set Set Set Set Set Set Set Set Set
  Set Set Set Set Set Set Set Set Set Set
  Set Set Set Set Set Set Set Set Set Set
  Set Set Set Set Set Set Set Set Set Set
  Set Set Set Set Set Set Set Set Set Set
  Set Set Set Set Set Set Set Set Set Set
  Set Set Set Set Set Set Set Set Set Set
  Set Set Set Set Set Set Set Set Set Set
  Set Set Set Set Set Set Set Set Set Set
  Set Set Set Set Set Set Set Set Set Set
  Set Set Set Set Set Set Set Set Set Set
  Set Set Set Set Set Set Set Set Set Set
  Set Set Set Set Set Set Set Set Set Set
  Set Set Set Set Set Set Set Set Set Set
  Set Set Set Set Set Set Set Set Set Set
  Set Set Set Set Set Set Set Set Set Set
  Set Set Set Set Set Set Set Set Set Set
  Set Set Set Set Set Set Set Set Set Set
  Set Set Set Set Set Set Set Set Set Set
  Set Set Set Set Set Set Set Set Set Set
  Set Set Set Set Set Set Set Set Set Set
  Set Set Set Set Set Set Set Set Set Set
  Set Set Set Set Set Set Set Set Set Set
  Set Set Set Set Set Set Set Set Set Set
  Set Set Set Set Set Set Set Set Set Set
  Set Set Set Set Set Set Set Set Set Set
  Set Set Set Set Set Set Set Set Set Set
  Set Set Set Set Set Set Set Set Set Set
  Set Set Set Set Set Set Set Set Set Set
  Set Set Set Set Set Set Set Set Set Set
  Set Set Set Set Set Set Set Set Set Set
  Set Set Set Set Set Set Set Set Set Set
  Set Set Set Set Set Set Set Set Set Set
  Set Set Set Set Set Set Set Set Set Set
  Set Set Set Set Set Set Set Set Set Set
  Set Set Set Set Set Set Set Set Set Set
  Set Set Set Set Set Set Set Set Set Set
  Set Set Set Set Set Set Set Set Set Set
  Set Set Set Set Set Set Set Set Set Set
  Set Set Set Set Set Set Set Set Set Set
  Set Set Set Set Set Set Set Set Set Set
  Set Set Set Set Set Set Set Set Set Set
  Set Set Set Set Set Set Set Set Set Set
  Set Set Set Set Set Set Set Set Set Set
  Set Set Set Set Set Set Set Set Set Set
  Set Set Set Set Set Set Set Set Set Set
  Set Set Set Set Set Set Set Set Set Set
  Set Set Set Set Set Set Set Set Set Set
  Set Set Set Set Set Set Set Set Set Set
  Set Set Set Set Set Set Set Set Set Set
  Set Set Set Set Set Set Set Set Set Set
  Set Set Set Set Set Set Set Set Set Set
  Set Set Set Set Set Set Set Set Set Set
  Set Set Set Set Set Set Set Set Set Set
  Set Set Set Set Set Set Set Set Set Set
  Set Set Set Set Set Set Set Set Set Set
  Set Set Set Set Set Set Set Set Set Set
  Set Set Set Set Set Set Set Set Set Set
  Set Set Set Set Set Set Set Set Set Set
  Set Set Set Set Set Set Set Set Set Set
  Set Set Set Set Set Set Set Set Set Set
  Set Set Set Set Set Set Set Set Set Set
  Set Set Set Set Set Set Set Set Set Set
  Set Set Set Set Set Set Set Set Set Set
  Set Set Set Set Set Set Set Set Set Set
  Set Set Set Set Set Set Set Set Set Set
  Set Set Set Set Set Set Set Set Set Set
  Set Set Set Set Set Set Set Set Set Set
  Set Set Set Set Set Set Set Set Set Set
  Set Set Set Set Set Set Set Set Set Set
  Set Set Set Set Set Set Set Set Set Set
