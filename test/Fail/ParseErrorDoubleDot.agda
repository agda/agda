-- Andreas, 2024-08-18
-- Check that expression '..' is a parse error and not an internal error.
-- Szumi, 2025-06-21
-- Adding a variable after '..' makes it parse, so the scope checker needs to reject it

f = ..x

-- Expected: Parse error
