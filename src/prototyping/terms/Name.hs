
module Name where

data Name = Name String Integer

instance Eq Name where
  Name _ i == Name _ j = i == j

instance Show Name where
  show (Name x i) = x ++ "_" ++ show i
