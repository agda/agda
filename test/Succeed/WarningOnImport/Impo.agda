module WarningOnImport.Impo where

B = Set
A = B

{-# WARNING_ON_USAGE A "Deprecated: Use B instead" #-}
{-# WARNING_ON_IMPORT "Deprecated: Use Impossible instead" #-}
