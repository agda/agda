-- Andreas, 2010-09-24

module ParseForallAbsurd where

parseFails : forall () -> Set1
parseFails x = Set
-- this does no longer give the error message
-- "absurd lambda cannot have a body"
