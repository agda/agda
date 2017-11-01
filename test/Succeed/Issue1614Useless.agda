-- The NO_POSITIVITY_CHECK pragma can only precede a mutual block or a
-- data/record definition.

module _ where

{-# NO_POSITIVITY_CHECK #-}
postulate Foo : Set
