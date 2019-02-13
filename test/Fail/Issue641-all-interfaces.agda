-- FNF, 2019-02-06
-- Test the difference between --ignore-interfaces and --ignore-all-interfaces
-- See Issue641-all-interfaces.flags and compare with Issue641.flags

module Issue641-all-interfaces where

-- Provoke a scope checking error.

open NoSuchModule

-- Expected output is some debug messages about importing, plus the error,
-- but in particular re-typechecking Agda.Primitive
