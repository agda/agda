open import Agda.Builtin.Reflection

postulate
  A : Set
  B : A → Set

macro
  foo : Term → TC _
  foo m = bindTC getContext \ cxt →
          inContext cxt (unify m (quoteTerm A))

test : ∀ x → B x → Set
test x y = foo
