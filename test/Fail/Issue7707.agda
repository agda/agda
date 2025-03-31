-- Andreas, 2025-03-31, issue #7707
-- Propositional squashing is only valid for 'data', not 'record'.
-- We did not have an explicit test case for the latter.

{-# OPTIONS --prop #-}

-- {-# OPTIONS -v tc.data.fits:100 #-}

data Exists {A : Set} (P : A → Prop) : Prop where
  mk : (w : A) → P w → Exists P

-- Should succeed (propositional squashing).

record ExR {A : Set} (P : A → Prop) : Prop where
  field
    witness : A
    prf     : P witness

-- Expected error: [ConstructorDoesNotFitInData]
-- Constructor ExR.constructor of inferred sort Set
-- does not fit into record type of sort Prop.
-- (Reason: Set is not less or equal than Prop)

data ExProp1 {A : Prop1} (P : A → Prop) : Prop where
  mk : (w : A) → P w → ExProp1 P

-- Expected error: [ConstructorDoesNotFitInData]
-- Constructor mk of inferred sort Prop₁
-- does not fit into data type of sort Set.
