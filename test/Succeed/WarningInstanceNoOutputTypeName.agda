-- Andreas, 2026-11-22, missing InstanceNoOutputTypeName warnings
postulate
   G : {{A : Set}} → Set  -- warning
   F : {{Set}} → Set      -- used to be no warning

variable
   {{A}} : Set            -- used to be warning

-- Expected warning InstanceNoOutputTypeName
-- for all three declarations.
