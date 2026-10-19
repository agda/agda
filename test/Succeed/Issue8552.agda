
open import Agda.Builtin.Equality

record IsPointed (A : Set) : Set where
  field
    point : A
open IsPointed {{...}}

record PointedSet : Set1 where
  field
    Carrier : Set
    instance
      {{IsPointed[Carrier]}} : IsPointed Carrier
open PointedSet

record PointedFunction (Aa Bb : PointedSet) : Set where
  open PointedSet Aa renaming (Carrier to AA)
  open PointedSet Bb renaming (Carrier to BB)
  field
    run : AA -> BB
    preserves-point : run point ≡ point
