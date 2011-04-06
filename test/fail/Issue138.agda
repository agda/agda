-- records not allowed in mutual blocks

module Issue138 where

mutual
  B = Set
  record Foo : Set where


