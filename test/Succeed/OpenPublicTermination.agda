
-- There was a bug where reexported constructors weren't
-- properly translated when termination checking.
module OpenPublicTermination where

 module A where
   data U : Set where
     nat  : U
     list : U -> U

 module A' where
   open A public

 open A'

 f : U -> U
 f nat = nat
 f (list nat) = nat
 f (list (list u)) = f (list u)

