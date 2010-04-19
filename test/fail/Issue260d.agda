-- Module shadowing using generated modules for records and datatypes
module Issue260d where

data D : Set where
module D where
