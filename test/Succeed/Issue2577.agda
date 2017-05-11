
postulate
  Wrap : Set → Set
  instance wrap : {A : Set} → A → Wrap A

postulate
  I : Set
  P : I → Set

HO = ∀ {i} {{p : P i}} → P i

postulate
  X : {{ho : HO}} → Set
  Y : {{ho : Wrap HO}} → Set

Works : Set
Works = X

-- Debug output shows messed up deBruijn indices in unwrapped target: P p instead of P i
Fails : Set
Fails = Y
