open import Agda.Primitive
open import Agda.Primitive.Cubical

record Wrap : Set (lsuc lzero) where
  field
    A : IUniv
