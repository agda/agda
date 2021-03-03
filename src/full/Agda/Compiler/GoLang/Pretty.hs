module Agda.Compiler.GoLang.Pretty where

import qualified Agda.Utils.Haskell.Syntax as HS
import Data.List ( intercalate )
import qualified Agda.Compiler.GoLang.Syntax as Go
import Text.PrettyPrint (empty)
import Agda.Utils.Hash
import Agda.Utils.Impossible

import Agda.Compiler.MAlonzo.Encode
import Agda.Utils.Pretty


prettyPrintGo :: Pretty a => a -> String
prettyPrintGo = show . pretty

instance Pretty Go.Module where
  pretty (Go.Module m imports imps) =
    vcat [ "package" <+> pretty m
         , ""
         , vcat $ map pretty imps
         , ""]

instance Pretty Go.Exp where
  prettyPrec pr e =
    case e of
      Go.GoInterface id -> "type" <+> pretty id <+> "interface{}"
      Go.GoStruct id elems -> "type" <+> pretty id <+> "struct {" <+> (vcat $ map pretty elems) <+> "}"
      Go.GoStructElement localId typeId -> "_" <+> pretty localId <+> pretty typeId <+> ";"
      _ -> fwords ""
      
instance Pretty Go.MemberId where
  pretty (Go.MemberId  s) = text s
  pretty (Go.MemberIndex i c) = text ""


instance Pretty Go.GlobalId where
  pretty (Go.GlobalId m) = fwords $ show $ intercalate "_" m


instance Pretty Go.LocalId where
  pretty (Go.LocalId n) = text $ show n

instance Pretty Go.TypeId where
  pretty (Go.TypeId m) = text m
