module Issue317 (A : Set) where

postulate F : Set → Set

-- Try evaluating F A at the top-level:
--
-- 1,3-4
-- Not in scope:
--   A at 1,3-4
-- when scope checking A
--
-- OK, in that case the inferred type of F should be
-- (A : Set) → Set → Set, right? No, it isn't, it's Set → Set.
--
-- I think the parameters should be in scope when "top-level" commands
-- are executed, because these commands should behave in the same way
-- as commands executed in a top-level goal at the end of the module.
-- It seems as if the implementation of
-- Agda.Interaction.BasicOps.atTopLevel has to be modified.
