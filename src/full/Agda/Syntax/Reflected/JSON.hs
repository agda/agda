module Agda.Syntax.Reflected.JSON where

import Agda.Syntax.Common
import Agda.Syntax.Literal
import Agda.Syntax.Abstract.Name
import Agda.Syntax.Internal (Dom, domFromArg, argFromDom)
import Agda.Syntax.Reflected

import qualified Data.Text as T
import Agda.TypeChecking.Monad
import Agda.Interaction.JSON
import Agda.TypeChecking.Pretty
import qualified Agda.Interaction.JSON as JSON

instance DecodeTCM a => DecodeTCM (Dom a) where
  decodeTCM val = domFromArg <$> decodeTCM val

instance DecodeTCM Hiding where
  decodeTCM = withText "Hiding" $ \val ->
    case T.unpack val of
      "hidden"   -> pure Hidden
      "instance" -> pure (Instance NoOverlap)
      "visible"  -> pure NotHidden
      t          -> fail $ "Unknown hiding: " ++ t

instance EncodeTCM Hiding where
  encodeTCM Hidden = pure $ String "hidden"
  encodeTCM Instance{} = pure $ String "instance"
  encodeTCM NotHidden{} = pure $ String "visible"

instance DecodeTCM Relevance where
  decodeTCM = withText "Relevance" $ \val ->
    case T.unpack val of
      "relevant"   -> pure Relevant
      "irrelevant" -> pure Irrelevant
      "nonstrict"  -> pure NonStrict
      t            -> fail $ "Unknown relevance: " ++ t

instance EncodeTCM Relevance where
  encodeTCM Relevant   = "relevant"
  encodeTCM Irrelevant = "irrelevant"
  encodeTCM NonStrict  = "nonstrict"

instance DecodeTCM Quantity where
  decodeTCM = withText "Relevance" $ \val ->
    case T.unpack val of
      "zero"    -> pure $ Quantity0 Q0Inferred
      "omega"   -> pure $ Quantityω QωInferred
      t          -> fail $ "Unknown quantity: " ++ t

instance EncodeTCM Quantity where
  encodeTCM (Quantity0 _) = pure $ String "zero"
  encodeTCM (Quantityω _) = pure $ String "omega"
  encodeTCM (Quantity1 _) = pure $ String "one"

instance DecodeTCM ArgInfo where
  decodeTCM = withObject "ArgInfo" $ \val -> do
    vis <- val .: "hiding"
    rel <- val .: "relevance"
    quant <- val .: "quantity"
    pure defaultArgInfo{argInfoHiding = vis, argInfoModality = Modality rel quant Continuous}

instance EncodeTCM ArgInfo where
  encodeTCM ai = obj [ "hiding" @= argInfoHiding ai, "relevance" @= getRelevance ai, "quantity" @= getQuantity ai ]

instance DecodeTCM a => DecodeTCM (Arg a) where
  decodeTCM = withObject "Arg" $ \val -> Arg <$> val .: "argInfo" <*> val .: "unArg"

instance EncodeTCM a => EncodeTCM (Arg a) where
  encodeTCM (Arg i v) = obj [ "argInfo" @= i, "unArg" @= v ]

instance DecodeTCM a => DecodeTCM (Abs a) where
  decodeTCM = withObject "Abs" $ \val -> Abs <$> val .: "absName" <*> val .: "unAbs"

instance DecodeTCM a => DecodeTCM (Elim' a) where
  decodeTCM = withObject "Elim" $ \val -> (val .: "kind") >>= \case
    "Apply" -> val .: "unApply"
    kind -> typeError . GenericDocError =<< ("Unsupported kind of Elim':" <+> text kind)

instance DecodeTCM Literal where
  decodeTCM (JSON.String x) = pure $ LitString x
  decodeTCM x = withSum "Literal"
    [ ("LitNat",    fmap LitNat    . (.: "lit"))
    , ("LitWord64", fmap LitWord64 . (.: "lit"))
    , ("LitFloat",  fmap LitFloat . (.: "lit"))
    , ("LitString", fmap LitString . (.: "lit"))
    ] x

instance DecodeTCM QName where
  decodeTCM = withObject "QName" $ \val -> do
    (nm :: String) <- val .: "qnameName"
    QName
      <$> val .: "qnameModule"
      <*> (mkName_ <$> val .: "qnameId" <*> pure nm)

instance DecodeTCM ModuleName where
  decodeTCM = fmap MName . decodeTCM

instance DecodeTCM Name where
  decodeTCM = withObject "Name" $ \val -> do
    (nm :: String) <- val .: "nameName"
    flip mkName_ nm <$> (val .: "nameId")

instance DecodeTCM NameId where
  decodeTCM = withObject "NameId" $ \val -> NameId <$> (val .: "id") <*> (val .: "module")

instance DecodeTCM ModuleNameHash where
  decodeTCM = fmap ModuleNameHash . decodeTCM

instance DecodeTCM MetaId where
  decodeTCM = withObject "MetaId" $ \val -> MetaId <$> (val .: "id") <*> (val .: "module")

instance DecodeTCM Term where
  decodeTCM = withSum "Term"
    [ ("Var",     \v -> Var    <$> (v .: "var") <*> (v .: "elims"))
    , ("Con",     \v -> Con    <$> (v .: "con") <*> (v .: "elims"))
    , ("Def",     \v -> Def    <$> (v .: "def") <*> (v .: "elims"))
    , ("Meta",    \v -> Meta   <$> (v .: "meta") <*> (v .: "elims"))
    , ("Lam",     \v -> Lam    <$> (v .: "hiding") <*> (v .: "abs"))
    , ("Pi",      \v -> Pi     <$> (v .: "domain") <*> (v .: "abs"))
    , ("Sort",    \v -> Sort   <$> (v .: "sort"))
    , ("Lit",     \v -> Lit    <$> (v .: "lit"))
    , ("ExtLam",  \v -> ExtLam <$> (v .: "clauses") <*> (v .: "elims"))
    , ("Unknown", \v -> pure Unknown)
    ]

instance DecodeTCM Sort where
  decodeTCM = withSum "Sort"
    [ ("SetS",     \v -> SetS     <$> (v .: "level"))
    , ("LitS",     \v -> LitS     <$> (v .: "level"))
    , ("PropS",    \v -> PropS    <$> (v .: "level"))
    , ("PropLitS", \v -> PropLitS <$> (v .: "level"))
    , ("InfS",     \v -> InfS     <$> (v .: "level"))
    , ("UnknownS", \v -> pure UnknownS)
    ]

instance DecodeTCM Clause where
  decodeTCM = withSum "Clause"
    [ ("Clause", \v -> Clause <$> (v .: "clauseTel") <*> (v .: "clausePats") <*> (v .: "clauseRHS"))
    , ("AbsurdClause", \v -> AbsurdClause <$> (v .: "clauseTel") <*> (v .: "clausePats"))
    ]

instance DecodeTCM Pattern where
  decodeTCM = withSum "Pattern"
    [ ("ConP",    \v -> ConP <$> (v .: "con") <*> (v .: "patterns"))
    , ("DotP",    \v -> DotP <$> (v .: "dot"))
    , ("VarP",    \v -> VarP <$> (v .: "var"))
    , ("LitP",    \v -> LitP <$> (v .: "lit"))
    , ("AbsurdP", \v -> AbsurdP <$> (v .: "var"))
    , ("ProjP",   \v -> ProjP <$> (v .: "proj"))
    ]
