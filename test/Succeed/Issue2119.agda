open import Agda.Builtin.Reflection

t = quoteTerm (∀ {α} {A : Set α} -> A -> A)

macro
  m : Type -> Term -> TC _
  m = unify

idType = m t
