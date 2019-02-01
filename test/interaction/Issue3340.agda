
open import Agda.Builtin.Equality

postulate
  A : Set
  B : A → Set

variable
  a : A
  b : B a

postulate
  C : B a → Set

postulate
  f : (b : B a) → {!!}
  g : (c : C b) → {!!}

module _ (a′ : A) where
  postulate
    h : (b : B a) (b′ : B a′) → {!!}
    j : (b′ : B a) (c : C b) (c′ : C b′) → {!!}
