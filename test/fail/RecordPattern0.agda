test : Set → Set
test record{} = record{}

-- Record pattern at non-record type  Set
-- when checking that the clause test record {} = record {} has
-- type Set → Set
