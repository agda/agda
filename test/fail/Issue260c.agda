-- Module shadowing using generated modules for records and datatypes
module Issue260c where

record R : Set where
module R where
