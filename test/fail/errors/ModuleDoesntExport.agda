module ModuleDoesntExport where

module A where
  postulate C : Set

open A using (B; module P) renaming (D to C)

