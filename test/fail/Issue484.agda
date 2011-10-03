-- There was a bug where constructors of private datatypes were
-- not made private.
module Issue484 where

module A where
 private
   data Foo : Set where
     foo : Foo

foo′ = A.foo
