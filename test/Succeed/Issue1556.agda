-- Andreas, 2018-08-14, issue #1556
-- Rule out very dependent types by looking for recursive calls
-- in the types of definitions.
{-# OPTIONS --no-guardedness #-}

-- {-# OPTIONS -v term:20 -v rec.graph:80 #-}

A : Set
data D : A → Set      -- D --> A  (new!)
a : A                 -- a --> A  (new!)

A = D a               -- A --> D, a
data D where d : D a  -- TODO: D --> a
a = d                 -- a --> d

-- Should be rejected, e.g., by termination checker.
