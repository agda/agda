module ExportTestAgda where

open import Common.Prelude

itWorksText : String
itWorksText = "It works!"

{-# COMPILED_EXPORT itWorksText itWorksText #-}
