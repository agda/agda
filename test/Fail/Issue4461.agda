{-# OPTIONS -v impossible:100 #-}

data M : Set where
  m : (I : _) → (I → M) → M

-- inferred
-- m : (I : Set) → (I → M) → M

-- Expected error:
-- Constructor m
-- of sort univSort _4
-- does not fit into data type of sort Set.
-- (Reason: Agda.Primitive.lzero != Agda.Primitive.lsuc _7)
-- when checking that the type _4 of an argument to the constructor m
-- fits in the sort Set of the datatype.
