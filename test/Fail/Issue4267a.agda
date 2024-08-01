import Issue4267.M using ()

-- foo : {!Issue4267.M.R!} -- WAS: cannot give, but this is the solution
foo = record { f = Set}

-- Expected error:
--
-- There is no known record with the field f
--
-- (The record field is not imported, not even in scope qualified.)
