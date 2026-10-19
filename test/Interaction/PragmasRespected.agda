{-# OPTIONS --show-implicit #-}

module PragmasRespected where

postulate
  Foo : {A : Set₁} → Set
  Bar : Foo {A = Set}

-- Andreas, 2014-10-20, AIM XX:
-- This test used to check that the --show-implicit option
-- is turned on even if the module is just reloaded from
-- an interface file.
-- However, as we now always recheck when reload,
-- this test should now trivially succeed.
