{-# OPTIONS_GHC -Wunused-imports #-}

------------------------------------------------------------------------
-- Pretty-printing of Haskell modules
------------------------------------------------------------------------

module Agda.Compiler.MAlonzo.Pretty where

import qualified Agda.Utils.Haskell.Syntax as HS
import Text.PrettyPrint (empty)

import Agda.Compiler.MAlonzo.Encode
import Agda.Utils.Function (applyWhen)
import Agda.Utils.Pretty


prettyPrint :: Pretty a => a -> String
prettyPrint = show . pretty

instance Pretty HS.Module where
  pretty (HS.Module m pragmas imps decls) =
    vcat $ concat
      [ map pretty pragmas
      , [ "" | not $ null pragmas ]
      , [ "module" <+> pretty m <+> "where" ]
      , [ "" ]
      , map pretty imps
      , [ "" ]
      , map pretty decls
      ]

instance Pretty HS.ModulePragma where
  pretty (HS.LanguagePragma ps) =
    "{-#" <+> "LANGUAGE" <+> fsep (punctuate comma $ map pretty ps) <+> "#-}"
  pretty (HS.OtherPragma p) =
    text p

instance Pretty HS.ImportDecl where
  pretty HS.ImportDecl{ HS.importModule    = m
                      , HS.importQualified = q
                      , HS.importSpecs     = specs } =
      hsep [ "import"
           , if q then "qualified" else empty
           , pretty m
           , maybe empty prSpecs specs ]
    where prSpecs (hide, specs) =
            hsep [ if hide then "hiding" else empty
                 , parens $ fsep $ punctuate comma $ map pretty specs ]

instance Pretty HS.ImportSpec where
  pretty (HS.IVar x) = pretty x

instance Pretty HS.Decl where
  pretty = \case
    HS.TypeDecl f xs t ->
      sep [ "type" <+> pretty f <+> fsep (map pretty xs) <+> "="
          , nest 2 $ pretty t ]
    HS.DataDecl newt d xs cons derv ->
      sep [ pretty newt <+> pretty d <+> fsep (map pretty xs)
          , nest 2 $ if null cons then empty
                     else "=" <+> fsep (punctuate " |" $ map pretty cons)
          , nest 2 $ prDeriving derv ]
      where
        prDeriving [] = empty
        prDeriving ds = "deriving" <+> parens (fsep $ punctuate comma $ map prDer ds)
        prDer (d, ts) = pretty (foldl HS.TyApp (HS.TyCon d) ts)
    HS.TypeSig fs t ->
      sep [ hsep (punctuate comma (map pretty fs)) <+> "::"
          , nest 2 $ pretty t ]
    HS.FunBind ms -> vcat $ map pretty ms
    HS.LocalBind s f rhs ->
      sep [ pretty s <> pretty f
          , nest 2 $ prettyRhs "=" rhs
          ]
    HS.PatSyn p1 p2 -> sep [ "pattern" <+> pretty p1 <+> "=" <+> pretty p2 ]
    HS.FakeDecl s -> text s
    HS.Comment s -> vcat $ map (("--" <+>) . text) (lines s)

instance Pretty HS.ConDecl where
  pretty (HS.ConDecl c sts) =
    pretty c <+>
    fsep (map (\(s, t) -> maybe empty pretty s <> prettyPrec 10 t) sts)

instance Pretty HS.Strictness where
  pretty HS.Strict = "!"
  pretty HS.Lazy   = empty

instance Pretty HS.Match where
  pretty (HS.Match f ps rhs wh) =
    prettyWhere wh $
      sep [ pretty f <+> fsep (map (prettyPrec 10) ps)
          , nest 2 $ prettyRhs "=" rhs ]

prettyWhere :: Maybe HS.Binds -> Doc -> Doc
prettyWhere Nothing  doc = doc
prettyWhere (Just b) doc =
  vcat [ doc, nest 2 $ sep [ "where", nest 2 $ pretty b ] ]

instance Pretty HS.Pat where
  prettyPrec pr pat =
    case pat of
      HS.PVar x         -> pretty x
      HS.PLit l         -> prettyPrec pr l
      HS.PAsPat x p     -> mparens (pr > 10) $ pretty x <> "@" <> prettyPrec 11 p
      HS.PWildCard      -> "_"
      HS.PBangPat p     -> "!" <> prettyPrec 11 p
      HS.PApp c ps      -> mparens (pr > 9) $ pretty c <+> hsep (map (prettyPrec 10) ps)
      HS.PatTypeSig p t -> mparens (pr > 0) $ sep [ pretty p <+> "::", nest 2 $ pretty t ]
      HS.PIrrPat p      -> mparens (pr > 10) $ "~" <> prettyPrec 11 p

prettyRhs :: String -> HS.Rhs -> Doc
prettyRhs eq (HS.UnGuardedRhs e)   = text eq <+> pretty e
prettyRhs eq (HS.GuardedRhss rhss) = vcat $ map (prettyGuardedRhs eq) rhss

prettyGuardedRhs :: String -> HS.GuardedRhs -> Doc
prettyGuardedRhs eq (HS.GuardedRhs ss e) =
    sep [ "|" <+> sep (punctuate comma $ map pretty ss) <+> text eq
        , nest 2 $ pretty e ]

instance Pretty HS.Binds where
  pretty (HS.BDecls ds) = vcat $ map pretty ds

instance Pretty HS.DataOrNew where
  pretty HS.DataType = "data"
  pretty HS.NewType  = "newtype"

instance Pretty HS.TyVarBind where
  pretty (HS.UnkindedVar x) = pretty x

instance Pretty HS.Type where
  prettyPrec pr t =
    case t of
      HS.TyForall xs t ->
        mparens (pr > 0) $
          sep [ ("forall" <+> fsep (map pretty xs)) <> "."
              , nest 2 $ pretty t ]
      HS.TyFun a b ->
        mparens (pr > 4) $
          sep [ prettyPrec 5 a <+> "->", prettyPrec 4 b ]
      HS.TyCon c -> pretty c
      HS.TyVar x -> pretty x
      HS.TyApp (HS.TyCon (HS.UnQual (HS.Ident "[]"))) t ->
        brackets $ pretty t
      t@HS.TyApp{} ->
        mparens (pr > 9) $
          sep [ prettyPrec 9 f
              , nest 2 $ fsep $ map (prettyPrec 10) ts ]
        where
          f : ts = appView t []
          appView (HS.TyApp a b) as = appView a (b : as)
          appView t as = t : as
      HS.FakeType s -> text s

instance Pretty HS.Stmt where
  pretty (HS.Qualifier e) = pretty e
  pretty (HS.Generator p e) = sep [ pretty p <+> "<-", nest 2 $ pretty e ]

instance Pretty HS.Literal where
  prettyPrec pr = \case
    HS.Int n    -> parensIfNeg n $ integer n
    HS.Frac x   -> parensIfNeg d $ double d
                   where
                   d = fromRational x
    HS.Char c   -> text (show c)
    HS.String s -> text (show s)
    where
    parensIfNeg :: (Ord n, Num n) => n -> Doc -> Doc
    parensIfNeg x = applyWhen (x < 0) $ mparens (pr > 10)

instance Pretty HS.Exp where
  prettyPrec pr e =
    case e of
      HS.Var x -> pretty x
      HS.Con c -> pretty c
      HS.Lit l -> pretty l
      HS.InfixApp a qop b -> mparens (pr > 0) $
        sep [ prettyPrec 1 a
            , pretty qop <+> prettyPrec 1 b ]
      HS.Ann e ty -> mparens (pr > 0) $
        sep [ prettyPrec 1 e
            , "::"
            , prettyPrec 1 ty
            ]
      HS.App{} -> mparens (pr > 9) $
        sep [ prettyPrec 9 f
            , nest 2 $ fsep $ map (prettyPrec 10) es ]
        where
          f : es = appView e []
          appView (HS.App f e) es = appView f (e : es)
          appView f es = f : es
      HS.Lambda ps e -> mparens (pr > 0) $
        sep [ "\\" <+> fsep (map (prettyPrec 10) ps) <+> "->"
            , nest 2 $ pretty e ]
      HS.Let bs e -> mparens (pr > 0) $
        sep [ "let" <+> pretty bs <+> "in"
            , pretty e ]
      HS.If a b c -> mparens (pr > 0) $
        sep [ "if" <+> pretty a
            , nest 2 $ "then" <+> pretty b
            , nest 2 $ "else" <+> prettyPrec 1 c ]
      HS.Case e bs -> mparens (pr > 0) $
        vcat [ "case" <+> pretty e <+> "of"
             , nest 2 $ vcat $ map pretty bs ]
      HS.ExpTypeSig e t -> mparens (pr > 0) $
        sep [ pretty e <+> "::"
            , nest 2 $ pretty t ]
      HS.NegApp exp -> parens $ "-" <> pretty exp
      HS.FakeExp s -> text s

instance Pretty HS.Alt where
  pretty (HS.Alt pat rhs wh) =
    prettyWhere wh $
      sep [ pretty pat, nest 2 $ prettyRhs "->" rhs ]

instance Pretty HS.ModuleName where
  pretty m = text s
    where HS.ModuleName s = encodeModuleName m

instance Pretty HS.QName where
  pretty q = mparens (isOperator q) (prettyQName q)

instance Pretty HS.Name where
  pretty (HS.Ident  s) = text s
  pretty (HS.Symbol s) = text s

instance Pretty HS.QOp where
  pretty (HS.QVarOp x)
    | isOperator x = prettyQName x
    | otherwise    = "`" <> prettyQName x <> "`"

isOperator :: HS.QName -> Bool
isOperator q =
  case q of
    HS.Qual _ x           -> isOp x
    HS.UnQual x           -> isOp x
  where
    isOp HS.Symbol{} = True
    isOp HS.Ident{}  = False

prettyQName :: HS.QName -> Doc
prettyQName (HS.Qual m x)           = pretty m <> "." <> pretty x
prettyQName (HS.UnQual x)           = pretty x
