module ExportTestAgda where

open import Common.Prelude

itWorksText : String
itWorksText = "It works!"

{-# COMPILE GHC itWorksText as itWorksText #-}
