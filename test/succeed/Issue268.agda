-- {-# OPTIONS -v tc.polarity:15 -v tc.pos:50 #-}
module Issue268 where

module Example₁ where
  open import Common.Coinduction

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
  -- Andreas, 2012-09-14
  -- with polarity Nonvariant, Agda recognizes id as a constant function
  -- since there is no proper match on the argument (Stream is a unit type)
  -- (if Data is opened, then there is a match on `cons')


  postulate
    P  : Stream → Set
    f  : ∀ xs → P (id xs) → Set
    xs : Stream
    p  : P (id xs)

  Foo : Set
  Foo = f xs p -- f _ p  -- Andreas: _ is not solved for since id is constant

  -- The code type checks when Data is opened, but not when Record is
  -- opened:
  --
  -- Bug.agda:34,11-12
  -- (Stream.tail (id xs)) != (.Bug.♯-0 _40) of type (∞ Stream)
  -- when checking that the expression p has type P (id (cons _40))

module Example₂ where

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
