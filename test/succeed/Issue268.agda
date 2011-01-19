module Issue268 where

module A where

  open import Coinduction

  module Record where

    record Stream : Set where
      constructor cons
      field
        tail : ∞ Stream

  module Data where

    data Stream : Set where
      cons : ∞ Stream → Stream

  -- open Data
  open Record

  id : Stream → Stream
  id (cons xs) = cons (♯ id (♭ xs))

  postulate
    P  : Stream → Set
    f  : ∀ xs → P (id xs) → Set
    xs : Stream
    p  : P (id xs)

  Foo : Set
  Foo = f _ p

module B where

  data D : Set where
    d : D

  id : D → D
  id d = d

  module Record where

    record E : Set where
      constructor e
      field
        f : D

  module Data where

    data E : Set where
      e : D → E

  -- open Data
  open Record

  id′ : E → E
  id′ (e xs) = e (id xs)

  postulate
    P : E → Set
    f : (x : E) → P (id′ x) → Set
    x : E
    p : P (id′ x)

  Foo : Set
  Foo = f _ p
