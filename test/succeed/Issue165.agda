
-- There was a problem with open public in parameterised modules.
module Issue165 where

postulate X : Set

module M where
  postulate P : Set

module R₀ (X : Set) where
  open M public

module R₁ (X : Set) where
  open R₀ X public

open R₁ X
postulate p : P
