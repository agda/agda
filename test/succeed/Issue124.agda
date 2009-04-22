
module Issue124 where

module A where
  data A : Set where
    c : A

module B where
  data B : Set where
    c : B

module C where
  open A public
  open B public

open C

f : B → B
f c = c