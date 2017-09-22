
data ⊤ : Set where tt : ⊤

postulate
  IndexL        : Set
  Ordered       : IndexL → Set
  ¬ho-shr-morph : IndexL → IndexL
  pres-¬ord     : ∀ ind → Ordered (¬ho-shr-morph ind)
  ¬ord-morph    : ∀ ind → Ordered ind → Set

postulate tt' : ⊤

poo : ∀ ind → ¬ord-morph (¬ho-shr-morph ind) (pres-¬ord ind)
poo ind with tt | ¬ho-shr-morph ind
... | _ | _ = {!!}
