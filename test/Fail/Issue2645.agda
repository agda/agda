-- Andreas, 2017-07-13, issue #2645

-- Agda accepted this definition:

record S : Set₁ where
  postulate
    field
      f : Set  -- Now: error raised here

s : Set → S
s A = record {f = A }
