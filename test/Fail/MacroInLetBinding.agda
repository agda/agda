-- Andreas, 2024-08-28
-- Trigger error NotAValidLetBinding.MacrosNotAllowed

f = let macro g = Set in Set

-- Expected error:
-- Macros cannot be defined in let bindings
