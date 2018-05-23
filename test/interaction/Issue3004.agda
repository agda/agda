
module _ where

module Test₁ where
  postulate
    id : {X : Set} → X → X
    A : Set
    x : A

  record S : Set where
    field
      a : A

  postulate
    B : S → Set

  record T : Set where
    field
      s : S
      b : B s

  -- Agda hangs here
  t : T
  t = λ
    { .T.s .S.a → x
    ; .T.b      → id {!!}
    }

module Test₂ where
  postulate
    id : (X : Set) → X → X
    A : Set
    B : A → Set
    x : A

  record T : Set where
    field
      a : A
      b : B a

  -- Agda hangs here
  t : T
  t = λ
    { .T.a → x
    ; .T.b → id {!!} {!!}
    }
