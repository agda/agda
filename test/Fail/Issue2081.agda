
-- Andreas, 2016-07-08, issue reported by Nisse

module Issue2081 where

module M where

  private

    Private : Set₁
    Private = Set
      -- The local module should be private as well!
      module Public where
        -- The definitions inside this module should not be private
        -- unless declared so explicitly!
        Public : Set₁
        Public = Set

  private
    Bla = Public -- should work!
      -- This `where` should not give a 'useless private' error:
      where open Public

module Pu = M.Public -- should fail!
