{-# OPTIONS --safe #-}

data A : Set

data A : Set where

-- WAS: only [MissingDefinitions] error
-- NOW: both [MissingDefinitions] and [ClashingDefinition]
-- could be better if it only showed [ClashingDefinition]
