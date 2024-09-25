module AnonymousRecConstrAmbig where

data Foo : Set where
  mk : Foo

data Bar : Set where
  mk : Bar

_ = mk.constructor
