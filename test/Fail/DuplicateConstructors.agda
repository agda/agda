
module DuplicateConstructors where

data D : Set where
  c : D
  c d d : D
  e e : D

f : D -> D
f c = c

-- error: [DuplicateConstructors]
-- Duplicate constructors in datatype: c d e
-- when scope checking the declaration
--   data D where
--     c : D
--     c : D
--     d : D
--     d : D
--     e : D
--     e : D
