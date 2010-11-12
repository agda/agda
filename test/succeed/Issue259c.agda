
module Issue259c where

postulate
  A : Set
  a : A
  b : ({x : A} → A) → A
  C : A → Set

d : {x : A} → A
d {x} = a

e : A
e = b (λ {x} → d {x})
  -- This shouldn't really be eta contracted
  -- but we're eta contracting it anyway
  -- The reason is that eta contraction helps
  -- alot in with abstractions, so we rather be
  -- a little too aggressive than too conservative.
  -- It doesn't make sense for the argument to d
  -- to be implicit here anyway, if it could be
  -- inferred from the type eta contraction wouldn't
  -- be a problem (see test/succeed/Issue259b.agda)

F : C e → Set₁
F _ with Set
F _ | _ = Set
