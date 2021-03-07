module Agda.Compiler.GoLang.Pretty where

import qualified Agda.Utils.Haskell.Syntax as HS
import Data.List ( intercalate )
import qualified Agda.Compiler.GoLang.Syntax as Go
import Text.PrettyPrint (empty)
import Agda.Utils.Hash
import Agda.Utils.Impossible
import Agda.Syntax.Common ( Nat )
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
      Go.String s -> "Str" <+> "ing"
      Go.GoFunction signatures body -> (vcat $ map pretty signatures) <+> (pretty body) <+> (text $ concat $ replicate (length signatures) "}\n")
      Go.GoSwitch (Go.LocalId v) cases -> (fwords "switch type") <> (fwords (show v)) <> (fwords "  := _") <> (fwords (show v)) <> (fwords ".(type) {") <> (vcat $ map pretty cases) <> (fwords "default: _ =\ \type") <> (fwords (show v)) <> (fwords ";\n panic(\"Unreachable\")")
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
  pretty (Go.ConstructorType m n) = text m <+> text n <+> ";"
  pretty (Go.FunctionType m n) = "(" <+> text m <+> text n <+> ")"
  pretty (Go.FunctionReturnElement m) = " func(" <+> text m <+> ")"
  pretty (Go.EmptyFunctionParameter) = "()"
  pretty (Go.EmptyType) = text ""

instance Pretty Go.GoFunctionSignature where
  pretty (Go.OuterSignature name param returnElems returnType) = "func " <> (pretty name) <> (pretty param) <> (vcat $ map pretty returnElems) <> " " <> (pretty returnType) <> " {"
  pretty (Go.InnerSignature param returnElems returnType) = "return func" <> (pretty param) <> (vcat $ map pretty returnElems) <> " " <> (pretty returnType) <> " {\n"



