------------------------------------------------------------------------
-- The Agda standard library
--
-- Showing booleans
------------------------------------------------------------------------

module Data.Bool.Show where

open import Data.Bool.Minimal using (Bool; false; true)
open import Data.String.Core using (String)

show : Bool → String
show true  = "true"
show false = "false"
