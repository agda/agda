-- The same name can not be exported more than once from a module.
module Issue154 where

module A where
  postulate X : Set

module B where
  postulate X : Set
  open A public
