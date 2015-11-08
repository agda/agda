-- named arguments should be allowed in module applications
module Issue420 where

module M {A : Set₁} where

open M {A = Set}
