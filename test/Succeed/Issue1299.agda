-- Andreas, 2014-10-09, issue reported by Matteo Acerbi

module _ where

module A where

module B (let module F = A) where

module C (let module F = A) where
-- Complains about duplicate F

-- Should work
