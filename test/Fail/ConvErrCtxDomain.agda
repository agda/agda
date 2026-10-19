module ConvErrCtxDomain where

postulate
  idh : ∀ {l} {A : Set l} {x : A} → Set
  A : Set
  B : A -> Set
  x : A
  y : B x

f : idh {x = ⦃ x : A ⦄ → B x} → idh {x = (x : A) → B x}
f x = x
