open import Agda.Builtin.String

x : String
{-# COMPILE GHC x = error "after decl but before defn" #-}
x = "some agda string"
{-# COMPILE GHC x = error "after decl and after defn" #-}
