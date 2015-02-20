module Agda.Syntax.Abstract.Name where

import {-# SOURCE #-} Agda.Syntax.Fixity (Fixity')

data Name

instance Show Name
instance Ord  Name

nameFixity :: Name -> Fixity'
