
module _ where

postulate
  A : Set
  _,_ : A → A → A

module M where
  module Mx (x : A) where
    module M where
      module My (y : A) where
        f : A
        f = x , y

postulate
  a b c : A

module M′  = M
module Ma  = M′.Mx.M a
module Mab = Ma.My b

g : A
g =  Mab.f
