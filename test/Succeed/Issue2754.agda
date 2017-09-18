-- Andreas, 2017-09-18, issue #2754 reported by nad.
-- Command line options
--
--   --ignore-interfaces -v tc:10
--
-- caused internal error when processing Agda.Primitive.
--
-- Reason: trying to debug print levels while level built-ins
-- are not yet bound.
--
-- Should work now, printing
--
--   .#Lacking_Level_Builtins#
--
-- where levels should be printed.


-- This file is left black intentionally.
