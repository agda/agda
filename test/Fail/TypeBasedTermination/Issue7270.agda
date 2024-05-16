-- Andreas, 2024-05-16, issue #7270

{-# OPTIONS --type-based-termination #-}

module TypeBasedTermination.Issue7270 where

record U : Set where
  coinductive
  field force : U
open U

postulate d : U → U

-- f is classified as size preserving, but is not, since d is unknown
-- Counterexamples: d = id; d u = u .force
--
f : U → U
f u = d u .force

-- This should not pass:
--
u : U
u .force = f u
