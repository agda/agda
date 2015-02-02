------------------------------------------------------------------------
-- The Agda standard library
--
-- Showing booleans
------------------------------------------------------------------------

module Data.Bool.Show where

open import Data.Bool.Base using (Bool; false; true)
open import Data.String.Base using (String)

show : Bool → String
show true  = "true"
show false = "false"
