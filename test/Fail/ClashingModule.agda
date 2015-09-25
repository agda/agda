-- You can't define the same module twice.
module ClashingModule where

module A where
module A where

open A
