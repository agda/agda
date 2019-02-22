{-# LANGUAGE DeriveDataTypeable         #-}

module Agda.Syntax.ImportDirective where

import Control.DeepSeq
import Data.Data (Data)

import Agda.Syntax.Common
import Agda.Syntax.Fixity
import Agda.Syntax.Position

-----------------------------------------------------------------------------
-- * Import directive
-----------------------------------------------------------------------------

-- | The things you are allowed to say when you shuffle names between name
--   spaces (i.e. in @import@, @namespace@, or @open@ declarations).
data ImportDirective' n m = ImportDirective
  { importDirRange :: Range
  , using          :: Using' n m
  , hiding         :: [ImportedName' n m]
  , impRenaming    :: [Renaming' n m]
  , publicOpen     :: Bool -- ^ Only for @open@. Exports the opened names from the current module.
  }
  deriving (Data, Eq)

data Renaming' n m = Renaming
  { renFrom    :: ImportedName' n m
    -- ^ Rename from this name.
  , renTo      :: ImportedName' n m
    -- ^ To this one.  Must be same kind as 'renFrom'.
  , renToRange :: Range
    -- ^ The range of the \"to\" keyword.  Retained for highlighting purposes.
  , fixity :: Maybe Fixity
  }
  deriving (Data, Eq)

-- | Default is directive is @private@ (use everything, but do not export).
defaultImportDir :: ImportDirective' n m
defaultImportDir = ImportDirective noRange UseEverything [] [] False

isDefaultImportDir :: ImportDirective' n m -> Bool
isDefaultImportDir (ImportDirective _ UseEverything [] [] False) = True
isDefaultImportDir _                                             = False

-- ** HasRange instances

instance (HasRange a, HasRange b) => HasRange (Renaming' a b) where
  getRange r = getRange (renFrom r, renTo r)


instance (HasRange a, HasRange b) => HasRange (ImportDirective' a b) where
  getRange = importDirRange


-- ** KillRange instances

instance (KillRange a, KillRange b) => KillRange (Renaming' a b) where
  killRange (Renaming i n _ f) = killRange2 (\i n -> Renaming i n noRange f) i n

instance (KillRange a, KillRange b) => KillRange (ImportDirective' a b) where
  killRange (ImportDirective _ u h r p) =
    killRange3 (\u h r -> ImportDirective noRange u h r p) u h r

-- ** NFData instances

-- | Ranges are not forced.

instance (NFData a, NFData b) => NFData (Renaming' a b) where
  rnf (Renaming a b _ _) = rnf a `seq` rnf b

instance (NFData a, NFData b) => NFData (ImportDirective' a b) where
  rnf (ImportDirective _ a b c _) = rnf a `seq` rnf b `seq` rnf c

