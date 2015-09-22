test : Set → Set
test record{ x = _ } = record{}

-- Record pattern at non-record type  Set
-- when checking that the clause test record { x = _ } = record {} has
-- type Set → Set
