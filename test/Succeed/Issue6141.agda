
module _ where

record R (N : Set) : Set₁ where
  field
    G : N → Set

open R {{...}}

module _ {N : Set} {{i : R N}} (g : (x : N) → G x)  where

  variable
    A : Set
    x : A

  works : G {N} x
  works {x = x} = g x

  works₂ : ∀ x → G x
  works₂ x = g x

  failed : G x
  failed {x = x} = g x
