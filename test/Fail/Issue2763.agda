
data ⊤ : Set where tt : ⊤

postulate
  A : Set
  B : A → Set
  a : A
  b : B a
  G : ∀ x → B x → Set

postulate tt' : ⊤

poo : G a b
poo with tt | a
... | _ | _ = {!!}
