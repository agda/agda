postulate
  X Y Z A : Set

record R : Set where
  field
    x : X
    y : Y
    z : Z

module M where
  postulate
    x : X
    y : Y

r : R
r = record { M; z = zz } where postulate zz : Z

-- Record update. Same as: record r { y = ... }
r2 : R
r2 = record { R r; y = y } where postulate y : Y

module M2 (a : A) where
 postulate
  w : Y
  z : Z

r3 : A → R
r3 a = record { M hiding (y); M2 a renaming (w to y) }
