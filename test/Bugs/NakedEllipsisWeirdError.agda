-- Andreas, 2019-08-10, weird error for naked ellipsis

...

-- Error (weird):
-- Missing type signature for left hand side ...
-- when scope checking the declaration
--   ...

-- When following the suggestion to give a type signature,
--
--   ... : Set
--
-- Agda says:
-- The ellipsis ... cannot have a type signature
-- <EOF><ERROR>
