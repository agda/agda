interleaved mutual

  data CoNat : Set
  record ∞CoNat : Set

  constructor
    zero : CoNat

  record ∞CoNat where
    coinductive
    field force : CoNat

  constructor
    suc : ∞CoNat → ?
