interleaved mutual

  data CoNat : Set
  record ∞CoNat : Set

  data _ where
    zero : CoNat

  record ∞CoNat where
    coinductive
    field force : CoNat

  data _ where
    suc : ∞CoNat → ?
