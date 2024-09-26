-- Andreas, 2024-09-26
-- Reproducer for JSBackend.BadCompilePragma

postulate A : Set

{-# COMPILE JS A #-}

-- Expected upon compilation with the JS Backend:
--
-- Badly formed COMPILE JS pragma. Expected
-- {-# COMPILE JS <name> = <js> #-}
