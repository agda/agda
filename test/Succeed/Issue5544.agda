
postulate
  Typ : Set
  ⊢   : Typ → Set
  N   : Typ
  t   : ⊢ N

record TopPred : Set where
  constructor tp
  field nf : Typ

postulate
  inv-t[σ] : (T : Typ) → ⊢ T → TopPred

su-I′ : TopPred → Typ
su-I′ krip =
    let tp _ = inv-t[σ] _ t
        open TopPred krip
    in N
