{-# OPTIONS -vtc.record.where:30 #-}
module Issue7805c where

postulate A : Set

record X : Set₁ where
  field it : {X : Set} → Set

-- This is a variant of #4131 and #655 using 'RecordWhere' to make sure
-- that we don't run into the same issues: field lets *should* insert
-- hidden arguments, and non-field lets should *not*.

-- Works if we have something to cause a direction change
complex : X
complex = record where it = let _ = Set in A

-- and otherwise
atomic : X
atomic = record where it = A

postulate any : {A : Set} → A

-- and doesn't needlessly instantiate non-field lets
nonfield : X
nonfield = record where
  yellow = any -- should not have any yellow here
  it = A
