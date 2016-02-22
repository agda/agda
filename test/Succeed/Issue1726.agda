
postulate
  U V W X Y Z : Set
  u : U
  v : V
  w : W
  x : X
  y : Y
  z : Z

module Top (u : U) where
  module A (v : V) where
    module M (w : W) where
      module O (x : X) where
      postulate O : X
    postulate O : X
  module B (y : Y) where
    open A public

module Test0 where
  module C = Top.B u y
  module D = C.M.O v w x
  O₁ : X
  O₁ = C.M.O v w
  O₂ : X
  O₂ = C.O v

module Test1 where
  module C (i g n o r i n g m e : Z) = Top.B u y
  module D = C.M.O z z z z z z z z z z v w x
  O : X
  O = C.M.O z z z z z z z z z z v w

module Test2 where
  module C (y : Y) = Top.B u y
  module D = C.M.O y v w x
  O : X
  O = C.M.O y v w

module Test3 where
  module C (z : Z) = Top.B u y
  module D = C.M.O z v w x
