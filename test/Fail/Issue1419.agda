module Issue1419 where

module A where
  module M where

module B where
  module M where

open A
open B

module N (let open M) where

  module LotsOfStuff where
