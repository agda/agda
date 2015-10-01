
module Agda.Interaction.Library.Base where

type LibName = String

data AgdaLibFile = AgdaLib
  { libName     :: LibName
  , libFile     :: FilePath
  , libIncludes :: [FilePath]
  , libDepends  :: [LibName]
  }
  deriving (Show)

