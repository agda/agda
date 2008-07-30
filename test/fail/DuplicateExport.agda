module DuplicateExport where

  module A where
    postulate x : Set

  module B where
    postulate x : Set

  open A public
  open B public