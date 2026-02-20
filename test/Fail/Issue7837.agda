module Issue7837 where

record R : Set₂ where
  field f g : Set₁

v : R
v = record where
      f = Set
      g = Set

r1 : R
r1 = record where
       open R v using (f; g) renaming (f to f; g to g)
                using (module ,) renaming (module , to ,)

-- Expected error: [RepeatedNamesInImportDirective]
-- Repeated names in import directive: module ,; f; g
-- when scope checking
-- record where
--   private
--     open
--       R v
--         using (f; g; module ,) renaming (f to f; g to g; module , to ,)
