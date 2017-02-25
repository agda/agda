{-# LANGUAGE DeriveDataTypeable   #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE StandaloneDeriving   #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
module Instances where

import           Agda.Syntax.Common
import qualified Agda.Syntax.Concrete        as C
import qualified Agda.Syntax.Fixity          as F
import           Agda.Syntax.Literal
import           Agda.Syntax.Notation
import           Agda.Syntax.Position
import           Agda.Syntax.Treeless
import           Agda.Utils.FileName
import           Data.Data
import           Data.Graph

deriving instance Data F.Fixity'
deriving instance Data F.PrecedenceLevel
deriving instance Data F.Associativity
deriving instance Data MetaId
deriving instance Data NameId
deriving instance Data C.NamePart
deriving instance Data C.Name
deriving instance Data Hiding
deriving instance Data Big
deriving instance Data Relevance
deriving instance Data Origin
deriving instance Data ArgInfo
deriving instance Data (Ranged RawName)
deriving instance Data (Named_ Int)
deriving instance Data (NamedArg Int)
deriving instance Data GenPart
deriving instance Data F.Fixity
deriving instance Data AbsolutePath
deriving instance Data (Position' ())
deriving instance Data (Interval' ())
deriving instance Data Range
deriving instance Data TError
deriving instance Data CaseType
deriving instance Data ModuleName
deriving instance Data Name
deriving instance Data TAlt
deriving instance Data Literal
deriving instance Data TPrim
deriving instance Data QName
deriving instance Data TTerm

deriving instance Typeable TTerm
deriving instance Show vertex => Show (SCC vertex)
