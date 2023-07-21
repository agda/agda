{-# OPTIONS_GHC -Wunused-imports #-}

------------------------------------------------------------------------
-- Top-level module names
------------------------------------------------------------------------

module Agda.Syntax.TopLevelModuleName where

import Control.DeepSeq

import Data.Function (on)
import Data.Hashable
import qualified Data.List as List
import Data.Text (Text)
import qualified Data.Text as T

import GHC.Generics (Generic)

import System.FilePath

import qualified Agda.Syntax.Abstract.Name as A
import Agda.Syntax.Common
import qualified Agda.Syntax.Concrete as C
import Agda.Syntax.Position

import Agda.Utils.BiMap (HasTag(..))
import Agda.Utils.FileName
import Agda.Utils.Hash
import Agda.Utils.Impossible
import Agda.Utils.Lens
import Agda.Utils.List1 (List1)
import qualified Agda.Utils.List1 as List1
import Agda.Utils.Pretty
import Agda.Utils.Singleton
import Agda.Utils.Size

------------------------------------------------------------------------
-- Raw top-level module names

-- | A top-level module name has one or more name parts.

type TopLevelModuleNameParts = List1 Text

-- | Raw top-level module names (with linear-time comparisons).

data RawTopLevelModuleName = RawTopLevelModuleName
  { rawModuleNameRange :: Range
  , rawModuleNameParts :: TopLevelModuleNameParts
  }
  deriving (Show, Generic)

instance Eq RawTopLevelModuleName where
  (==) = (==) `on` rawModuleNameParts

instance Ord RawTopLevelModuleName where
  compare = compare `on` rawModuleNameParts

instance Sized RawTopLevelModuleName where
  size = size . rawModuleNameParts
  natSize = natSize . rawModuleNameParts

instance Pretty RawTopLevelModuleName where
  pretty = text . rawTopLevelModuleNameToString

instance HasRange RawTopLevelModuleName where
  getRange = rawModuleNameRange

instance SetRange RawTopLevelModuleName where
  setRange r (RawTopLevelModuleName _ x) = RawTopLevelModuleName r x

instance KillRange RawTopLevelModuleName where
  killRange (RawTopLevelModuleName _ x) =
    RawTopLevelModuleName noRange x

instance C.IsNoName RawTopLevelModuleName where
  isNoName m = rawModuleNameParts m == singleton "_"

-- | The 'Range' is not forced.

instance NFData RawTopLevelModuleName where
  rnf (RawTopLevelModuleName _ x) = rnf x

-- | Turns a raw top-level module name into a string.

rawTopLevelModuleNameToString :: RawTopLevelModuleName -> String
rawTopLevelModuleNameToString =
  List.intercalate "." .
  map T.unpack . List1.toList . rawModuleNameParts

-- | Hashes a raw top-level module name.

hashRawTopLevelModuleName :: RawTopLevelModuleName -> ModuleNameHash
hashRawTopLevelModuleName =
  ModuleNameHash . hashString . rawTopLevelModuleNameToString

-- | Turns a qualified name into a 'RawTopLevelModuleName'. The
-- qualified name is assumed to represent a top-level module name.

rawTopLevelModuleNameForQName :: C.QName -> RawTopLevelModuleName
rawTopLevelModuleNameForQName q = RawTopLevelModuleName
  { rawModuleNameRange = getRange q
  , rawModuleNameParts =
      fmap (T.pack . C.nameToRawName) $ C.qnameParts q
  }

-- | Computes the 'RawTopLevelModuleName' corresponding to the given
-- module name, which is assumed to represent a top-level module name.
--
-- Precondition: The module name must be well-formed.

rawTopLevelModuleNameForModuleName ::
  A.ModuleName -> RawTopLevelModuleName
rawTopLevelModuleNameForModuleName (A.MName []) = __IMPOSSIBLE__
rawTopLevelModuleNameForModuleName (A.MName ms) =
  List1.ifNull ms __IMPOSSIBLE__ $ \ms ->
  RawTopLevelModuleName
    { rawModuleNameRange = getRange ms
    , rawModuleNameParts =
        fmap (T.pack . C.nameToRawName . A.nameConcrete) ms
    }

-- | Computes the top-level module name.
--
-- Precondition: The 'C.Module' has to be well-formed.
-- This means that there are only allowed declarations before the
-- first module declaration, typically import declarations.
-- See 'spanAllowedBeforeModule'.

rawTopLevelModuleNameForModule :: C.Module -> RawTopLevelModuleName
rawTopLevelModuleNameForModule (C.Mod _ []) = __IMPOSSIBLE__
rawTopLevelModuleNameForModule (C.Mod _ ds) =
  case C.spanAllowedBeforeModule ds of
    (_, C.Module _ _ n _ _ : _) -> rawTopLevelModuleNameForQName n
    _                           -> __IMPOSSIBLE__

------------------------------------------------------------------------
-- Top-level module names

-- | Top-level module names (with constant-time comparisons).

data TopLevelModuleName = TopLevelModuleName
  { moduleNameRange :: Range
  , moduleNameId    :: {-# UNPACK #-} !ModuleNameHash
  , moduleNameParts :: TopLevelModuleNameParts
  }
  deriving (Show, Generic)

instance HasTag TopLevelModuleName where
  type Tag TopLevelModuleName = ModuleNameHash
  tag = Just . moduleNameId

instance Eq TopLevelModuleName where
  (==) = (==) `on` moduleNameId

instance Ord TopLevelModuleName where
  compare = compare `on` moduleNameId

instance Hashable TopLevelModuleName where
  hashWithSalt salt = hashWithSalt salt . moduleNameId

instance Sized TopLevelModuleName where
  size = size . rawTopLevelModuleName
  natSize = natSize . rawTopLevelModuleName

instance Pretty TopLevelModuleName where
  pretty = pretty . rawTopLevelModuleName

instance HasRange TopLevelModuleName where
  getRange = moduleNameRange

instance SetRange TopLevelModuleName where
  setRange r (TopLevelModuleName _ h x) = TopLevelModuleName r h x

instance KillRange TopLevelModuleName where
  killRange (TopLevelModuleName _ h x) = TopLevelModuleName noRange h x

-- | The 'Range' is not forced.

instance NFData TopLevelModuleName where
  rnf (TopLevelModuleName _ x y) = rnf (x, y)

-- | A lens focusing on the 'moduleNameParts'.

lensTopLevelModuleNameParts ::
  Lens' TopLevelModuleName TopLevelModuleNameParts
lensTopLevelModuleNameParts f m =
  f (moduleNameParts m) <&> \ xs -> m{ moduleNameParts = xs }

-- | Converts a top-level module name to a raw top-level module name.

rawTopLevelModuleName :: TopLevelModuleName -> RawTopLevelModuleName
rawTopLevelModuleName m = RawTopLevelModuleName
  { rawModuleNameRange = moduleNameRange m
  , rawModuleNameParts = moduleNameParts m
  }

-- | Converts a raw top-level module name and a hash to a top-level
-- module name.
--
-- This function does not ensure that there are no hash collisions,
-- that is taken care of by
-- 'Agda.TypeChecking.Monad.State.topLevelModuleName'.

unsafeTopLevelModuleName ::
  RawTopLevelModuleName -> ModuleNameHash -> TopLevelModuleName
unsafeTopLevelModuleName m h = TopLevelModuleName
  { moduleNameRange = rawModuleNameRange m
  , moduleNameParts = rawModuleNameParts m
  , moduleNameId    = h
  }

-- | A corresponding 'C.QName'. The range of each 'Name' part is the
-- whole range of the 'TopLevelModuleName'.

topLevelModuleNameToQName :: TopLevelModuleName -> C.QName
topLevelModuleNameToQName m =
  List1.foldr C.Qual C.QName $
  fmap (C.Name (getRange m) C.NotInScope .
        C.stringNameParts . T.unpack) $
  moduleNameParts m

-- | Turns a top-level module name into a file name with the given
-- suffix.

moduleNameToFileName :: TopLevelModuleName -> String -> FilePath
moduleNameToFileName TopLevelModuleName{ moduleNameParts = ms } ext =
  joinPath (map T.unpack $ List1.init ms) </>
  T.unpack (List1.last ms) <.> ext

-- | Finds the current project's \"root\" directory, given a project
-- file and the corresponding top-level module name.
--
-- Example: If the module \"A.B.C\" is located in the file
-- \"/foo/A/B/C.agda\", then the root is \"/foo/\".
--
-- Precondition: The module name must be well-formed.

projectRoot :: AbsolutePath -> TopLevelModuleName -> AbsolutePath
projectRoot file TopLevelModuleName{ moduleNameParts = m } =
  mkAbsolute $
    iterate takeDirectory (filePath file) !! length m
