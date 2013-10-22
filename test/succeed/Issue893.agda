-- Andreas, 2013-10-22
-- Fixed by checking with-function-types in internal syntax!
module Issue893 where

  postulate
    S : Set

  data Dec (Px : Set) (q : Px → S) : Set where
    tt : Dec Px q

  -- record parameter is essential to reproduce error message
  record Rec (P : S → Set) : Set where
    field
      prop : {x : S} → P x → S

    bla : (x : S) → Dec (P x) prop
    bla x with x
    bla x | _ = tt
