{-# OPTIONS_GHC -fno-warn-orphans #-}

{-| Pretty printer for the concrete syntax.
-}
module Agda.Syntax.Concrete.Pretty
  ( module Agda.Syntax.Concrete.Pretty
  , module Agda.Syntax.Concrete.Glyph
  ) where

import Prelude hiding ( null )

import Data.Maybe
import qualified Data.Foldable  as Fold
import qualified Data.Semigroup as Semigroup
import qualified Data.Strict.Maybe as Strict
import qualified Data.Text as T

import Agda.Syntax.Common
import Agda.Syntax.Concrete
import Agda.Syntax.Concrete.Glyph

import Agda.Utils.Float (toStringWithoutDotZero)
import Agda.Utils.Function
import Agda.Utils.Functor
import Agda.Utils.List1 ( List1, pattern (:|) )
import qualified Agda.Utils.List1 as List1
import qualified Agda.Utils.List2 as List2
import Agda.Utils.Maybe
import Agda.Utils.Null
import qualified Agda.Syntax.Common.Aspect as Asp
import Agda.Syntax.Common.Pretty

import Agda.Utils.Impossible

deriving instance Show Expr
deriving instance (Show a) => Show (OpApp a)
deriving instance Show Declaration
deriving instance Show Pattern
deriving instance Show a => Show (Binder' a)
deriving instance Show TypedBinding
deriving instance Show LamBinding
deriving instance Show BoundName
deriving instance Show ModuleAssignment
deriving instance (Show a, Show b) => Show (ImportDirective' a b)
deriving instance (Show a, Show b) => Show (Using' a b)
deriving instance (Show a, Show b) => Show (Renaming' a b)
deriving instance Show Pragma
deriving instance Show RHS
deriving instance Show LHS
deriving instance Show LHSCore
deriving instance Show LamClause
deriving instance Show WhereClause
deriving instance Show ModuleApplication
deriving instance Show DoStmt
deriving instance Show Module

-- Lays out a list of documents [d₁, d₂, …] in the following way:
-- @
--   { d₁
--   ; d₂
--   ⋮
--   }
-- @
-- If the list is empty, then the notation @{}@ is used.

bracesAndSemicolons :: Foldable t => t Doc -> Doc
bracesAndSemicolons ts = case Fold.toList ts of
  []       -> "{}"
  (d : ds) -> sep (["{" <+> d] ++ map (";" <+>) ds ++ ["}"])

-- | @prettyHiding info visible doc@ puts the correct braces
--   around @doc@ according to info @info@ and returns
--   @visible doc@ if the we deal with a visible thing.
prettyHiding :: LensHiding a => a -> (Doc -> Doc) -> Doc -> Doc
prettyHiding a parens =
  case getHiding a of
    Hidden     -> braces'
    Instance{} -> dbraces
    NotHidden  -> parens

prettyRelevance :: LensRelevance a => a -> Doc -> Doc
prettyRelevance a = (pretty (getRelevance a) <>)

prettyQuantity :: LensQuantity a => a -> Doc -> Doc
prettyQuantity a = (pretty (getQuantity a) <+>)

prettyLock :: LensLock a => a -> Doc -> Doc
prettyLock a doc = case getLock a of
  IsLock LockOLock -> "@lock" <+> doc
  IsLock LockOTick -> "@tick" <+> doc
  IsNotLock -> doc

prettyErased :: Erased -> Doc -> Doc
prettyErased = prettyQuantity . asQuantity

prettyCohesion :: LensCohesion a => a -> Doc -> Doc
prettyCohesion a = (pretty (getCohesion a) <+>)

prettyTactic :: BoundName -> Doc -> Doc
prettyTactic = prettyTactic' . bnameTactic

prettyFiniteness :: BoundName -> Doc -> Doc
prettyFiniteness name
  | bnameIsFinite name = ("@finite" <+>)
  | otherwise = id

prettyTactic' :: TacticAttribute -> Doc -> Doc
prettyTactic' Nothing  d = d
prettyTactic' (Just t) d = "@" <> (parens ("tactic" <+> pretty t) <+> d)

instance (Pretty a, Pretty b) => Pretty (a, b) where
    pretty (a, b) = parens $ (pretty a <> comma) <+> pretty b

instance Pretty (ThingWithFixity Name) where
    pretty (ThingWithFixity n _) = pretty n

instance Pretty a => Pretty (WithHiding a) where
  pretty w = prettyHiding w id $ pretty $ dget w

instance Pretty Relevance where
  pretty Relevant   = empty
  pretty Irrelevant = "."
  pretty NonStrict  = ".."

instance Pretty Q0Origin where
  pretty = \case
    Q0Inferred -> empty
    Q0{}       -> "@0"
    Q0Erased{} -> "@erased"

instance Pretty Q1Origin where
  pretty = \case
    Q1Inferred -> empty
    Q1{}       -> "@1"
    Q1Linear{} -> "@linear"

instance Pretty QωOrigin where
  pretty = \case
    QωInferred -> empty
    Qω{}       -> "@ω"
    QωPlenty{} -> "@plenty"

instance Pretty Quantity where
  pretty = \case
    Quantity0 o -> ifNull (pretty o) "@0" id
    Quantity1 o -> ifNull (pretty o) "@1" id
    Quantityω o -> pretty o

instance Pretty Erased where
  pretty = pretty . asQuantity

instance Pretty Cohesion where
  pretty Flat   = "@♭"
  pretty Continuous = mempty
  pretty Squash  = "@⊤"

instance Pretty Modality where
  pretty mod = hsep
    [ pretty (getRelevance mod)
    , pretty (getQuantity mod)
    , pretty (getCohesion mod)
    ]

-- | Show the attributes necessary to recover a modality, in long-form
-- (e.g. using at-syntax rather than dots). For the default modality,
-- the result is at-ω (rather than the empty document). Suitable for
-- showing modalities outside of binders.
attributesForModality :: Modality -> Doc
attributesForModality mod
  | mod == defaultModality = text "@ω"
  | otherwise = fsep $ catMaybes [relevance, quantity, cohesion]
  where
    relevance = case getRelevance mod of
      Relevant   -> Nothing
      Irrelevant -> Just "@irrelevant"
      NonStrict  -> Just "@shape-irrelevant"
    quantity = case getQuantity mod of
      Quantity0{} -> Just "@0"
      Quantity1{} -> Just "@1"
      Quantityω{} -> Nothing
    cohesion = case getCohesion mod of
      Flat{}       -> Just "@♭"
      Continuous{} -> Nothing
      Squash{}     -> Just "@⊤"

instance Pretty (OpApp Expr) where
  pretty (Ordinary e) = pretty e
  pretty (SyntaxBindingLambda r bs e) = pretty (Lam r bs e)

instance Pretty a => Pretty (MaybePlaceholder a) where
  pretty Placeholder{}       = "_"
  pretty (NoPlaceholder _ e) = pretty e

instance Pretty Expr where
    pretty e =
        case e of
            Ident x          -> pretty x
            KnownIdent nk x  -> annotateAspect (Asp.Name (Just nk) False) (pretty x)
            Lit _ l          -> pretty l
            QuestionMark _ n -> hlSymbol "?" <> maybe empty (text . show) n
            Underscore _ n   -> maybe underscore text n
            App _ _ _        ->
                case appView e of
                    AppView e1 args     ->
                        fsep $ pretty e1 : map pretty args
--                      sep [ pretty e1
--                          , nest 2 $ fsep $ map pretty args
--                          ]
            RawApp _ es    -> fsep $ map pretty $ List2.toList es
            OpApp _ q _ es         -> fsep $ prettyOpApp (Asp.Name Nothing True) q es
            KnownOpApp nk _ q _ es -> fsep $ prettyOpApp (Asp.Name (Just nk) True) q es

            WithApp _ e es -> fsep $
              pretty e : map ((hlSymbol "|" <+>) . pretty) es

            HiddenArg _ e -> braces' $ pretty e
            InstanceArg _ e -> dbraces $ pretty e
            Lam _ bs (AbsurdLam _ h) -> lambda <+> fsep (fmap pretty bs) <+> absurd h
            Lam _ bs e ->
                sep [ lambda <+> fsep (fmap pretty bs) <+> arrow
                    , nest 2 $ pretty e
                    ]
            AbsurdLam _ h -> lambda <+> absurd h
            ExtendedLam _ e pes ->
              lambda <+>
              prettyErased e (bracesAndSemicolons (fmap pretty pes))
            Fun _ e1 e2 ->
                sep [ prettyCohesion e1 (prettyQuantity e1 (pretty e1)) <+> arrow
                    , pretty e2
                    ]
            Pi tel e ->
                sep [ pretty (Tel $ smashTel $ List1.toList tel) <+> arrow
                    , pretty e
                    ]
            Let _ ds me  ->
                sep [ hlKeyword "let" <+> vcat (fmap pretty ds)
                    , maybe empty (\ e -> hlKeyword "in" <+> pretty e) me
                    ]
            Paren _ e -> parens $ pretty e
            IdiomBrackets _ es ->
              case es of
                []   -> emptyIdiomBrkt
                [e]  -> leftIdiomBrkt <+> pretty e <+> rightIdiomBrkt
                e:es -> leftIdiomBrkt <+> pretty e <+> fsep (map (("|" <+>) . pretty) es) <+> rightIdiomBrkt
            DoBlock _ ss -> hlKeyword "do" <+> vcat (fmap pretty ss)
            As _ x e  -> pretty x <> hlSymbol "@" <> pretty e
            Dot _ e   -> hlSymbol "." <> pretty e
            DoubleDot _ e  -> hlSymbol ".." <> pretty e
            Absurd _  -> hlSymbol "()"
            Rec _ xs  -> sep [hlKeyword "record", bracesAndSemicolons (map pretty xs)]
            RecUpdate _ e xs ->
              sep [hlKeyword "record" <+> pretty e, bracesAndSemicolons (map pretty xs)]
            Quote _ -> hlKeyword "quote"
            QuoteTerm _ -> hlKeyword "quoteTerm"
            Unquote _  -> hlKeyword "unquote"
            Tactic _ t -> hlKeyword "tactic" <+> pretty t
            -- Andreas, 2011-10-03 print irrelevant things as .(e)
            DontCare e -> hlSymbol "." <> parens (pretty e)
            Equal _ a b -> pretty a <+> equals <+> pretty b
            Ellipsis _  -> hlSymbol "..."
            Generalized e -> pretty e
        where
          absurd NotHidden  = parens mempty
          absurd Instance{} = dbraces mempty
          absurd Hidden     = braces mempty

instance (Pretty a, Pretty b) => Pretty (Either a b) where
  pretty = either pretty pretty

instance Pretty a => Pretty (FieldAssignment' a) where
  pretty (FieldAssignment x e) = sep [ pretty x <+> "=" , nest 2 $ pretty e ]

instance Pretty ModuleAssignment where
  pretty (ModuleAssignment m es i) = fsep (pretty m : map pretty es) <+> pretty i

instance Pretty LamClause where
  pretty (LamClause ps rhs _) =
    sep [ fsep (map pretty ps)
        , nest 2 $ pretty' rhs
        ]
    where
      pretty' (RHS e)   = arrow <+> pretty e
      pretty' AbsurdRHS = empty

instance Pretty BoundName where
  pretty BName{ boundName = x } = pretty x

data NamedBinding = NamedBinding
  { withHiding   :: Bool
  , namedBinding :: NamedArg Binder
  }

isLabeled :: NamedArg Binder -> Maybe ArgName
isLabeled x
  | visible x              = Nothing  -- Ignore labels on visible arguments
  | Just l <- bareNameOf x = boolToMaybe (l /= nameToRawName (boundName $ binderName $ namedArg x)) l
  | otherwise              = Nothing

instance Pretty a => Pretty (Binder' a) where
  pretty (Binder mpat n) = let d = pretty n in case mpat of
    Nothing  -> d
    Just pat -> d <+> "@" <+> parens (pretty pat)

instance Pretty NamedBinding where
  pretty (NamedBinding withH x) = prH $
    if | Just l <- isLabeled x -> text l <+> "=" <+> pretty xb
       | otherwise             -> pretty xb

    where

    xb = namedArg x
    bn = binderName xb
    prH | withH     = prettyRelevance x
                    . prettyHiding x mparens
                    . prettyCohesion x
                    . prettyQuantity x
                    . prettyTactic bn
        | otherwise = id
    -- Parentheses are needed when an attribute @... is present
    mparens
      | noUserQuantity x, Nothing <- bnameTactic bn = id
      | otherwise = parens

instance Pretty LamBinding where
    pretty (DomainFree x) = pretty (NamedBinding True x)
    pretty (DomainFull b) = pretty b

instance Pretty TypedBinding where
    pretty (TLet _ ds) = parens $ "let" <+> vcat (fmap pretty ds)
    pretty (TBind _ xs (Underscore _ Nothing)) =
      fsep (fmap (pretty . NamedBinding True) xs)
    pretty (TBind _ xs e) = fsep
      [ prettyRelevance y
        $ prettyHiding y parens
        $ prettyFiniteness (binderName $ namedArg y)
        $ prettyCohesion y
        $ prettyQuantity y
        $ prettyLock y
        $ prettyTactic (binderName $ namedArg y) $
        sep [ fsep (map (pretty . NamedBinding False) ys)
            , ":" <+> pretty e ]
      | ys@(y : _) <- groupBinds $ List1.toList xs ]
      where
        groupBinds [] = []
        groupBinds (x : xs)
          | Just{} <- isLabeled x = [x] : groupBinds xs
          | otherwise   = (x : ys) : groupBinds zs
          where (ys, zs) = span (same x) xs
                same x y = getArgInfo x == getArgInfo y && isNothing (isLabeled y)

newtype Tel = Tel Telescope

instance Pretty Tel where
    pretty (Tel tel)
      | any isMeta tel = forallQ <+> fsep (map pretty tel)
      | otherwise      = fsep (map pretty tel)
      where
        isMeta (TBind _ _ (Underscore _ Nothing)) = True
        isMeta _ = False

smashTel :: Telescope -> Telescope
smashTel (TBind r xs e  :
          TBind _ ys e' : tel)
  | prettyShow e == prettyShow e' = smashTel (TBind r (xs Semigroup.<> ys) e : tel)
smashTel (b : tel) = b : smashTel tel
smashTel [] = []


instance Pretty RHS where
    pretty (RHS e)   = "=" <+> pretty e
    pretty AbsurdRHS = empty

instance Pretty WhereClause where
  pretty  NoWhere = empty
  pretty (AnyWhere _ [Module _ NotErased{} x [] ds])
    | isNoName (unqualify x)
                       = vcat [ "where", nest 2 (vcat $ map pretty ds) ]
  pretty (AnyWhere _ ds) = vcat [ "where", nest 2 (vcat $ map pretty ds) ]
  pretty (SomeWhere _ erased m a ds) =
    vcat [ hsep $ applyWhen (a == PrivateAccess UserWritten) ("private" :)
             [ "module", prettyErased erased (pretty m), "where" ]
         , nest 2 (vcat $ map pretty ds)
         ]

instance Pretty LHS where
  pretty (LHS p eqs es) = sep
    [ pretty p
    , nest 2 $ if null eqs then empty else fsep $ map pretty eqs
    , nest 2 $ prefixedThings "with" (map prettyWithd es)
    ] where

    prettyWithd :: WithExpr -> Doc
    prettyWithd (Named nm wh) =
      let e = pretty wh in
      case nm of
        Nothing -> e
        Just n  -> pretty n <+> ":" <+> e

instance Pretty LHSCore where
  pretty (LHSHead f ps) = sep $ pretty f : map (parens . pretty) ps
  pretty (LHSProj d ps lhscore ps') = sep $
    pretty d : map (parens . pretty) ps ++
    parens (pretty lhscore) : map (parens . pretty) ps'
  pretty (LHSWith h wps ps) = if null ps then doc else
      sep $ parens doc : map (parens . pretty) ps
    where
    doc = sep $ pretty h : map (("|" <+>) . pretty) wps
  pretty (LHSEllipsis r p) = "..."

instance Pretty ModuleApplication where
  pretty (SectionApp _ bs e) = fsep (map pretty bs) <+> "=" <+> pretty e
  pretty (RecordModuleInstance _ rec) = "=" <+> pretty rec <+> "{{...}}"

instance Pretty DoStmt where
  pretty (DoBind _ p e cs) =
    ((pretty p <+> "←") <?> pretty e) <?> prCs cs
    where
      prCs [] = empty
      prCs cs = "where" <?> vcat (map pretty cs)
  pretty (DoThen e) = pretty e
  pretty (DoLet _ ds) = "let" <+> vcat (fmap pretty ds)

instance Pretty Declaration where
  prettyList = vcat . map pretty
  pretty = \case
    TypeSig i tac x e ->
      sep [ prettyTactic' tac $ prettyRelevance i $ prettyCohesion i $ prettyQuantity i $ pretty x <+> ":"
          , nest 2 $ pretty e
          ]
    FieldSig inst tac x (Arg i e) ->
      mkInst inst $ mkOverlap i $
      prettyRelevance i $ prettyHiding i id $ prettyCohesion i $ prettyQuantity i $
      pretty $ TypeSig (setRelevance Relevant i) tac x e
      where
        mkInst (InstanceDef _) d = sep [ "instance", nest 2 d ]
        mkInst NotInstanceDef  d = d

        mkOverlap i d | isOverlappable i = "overlap" <+> d
                      | otherwise        = d
    Field _ fs ->
      sep [ "field"
          , nest 2 $ vcat (map pretty fs)
          ]
    FunClause lhs rhs wh _ ->
      sep [ pretty lhs
          , nest 2 $ pretty rhs
          ] $$ nest 2 (pretty wh)
    DataSig _ erased x tel e ->
      sep [ hsep  [ "data"
                  , prettyErased erased (pretty x)
                  , fcat (map pretty tel)
                  ]
          , nest 2 $ hsep
                  [ ":"
                  , pretty e
                  ]
          ]
    Data _ erased x tel e cs ->
      sep [ hsep  [ "data"
                  , prettyErased erased (pretty x)
                  , fcat (map pretty tel)
                  ]
          , nest 2 $ hsep
                  [ ":"
                  , pretty e
                  , "where"
                  ]
          ] $$ nest 2 (vcat $ map pretty cs)
    DataDef _ x tel cs ->
      sep [ hsep  [ "data"
                  , pretty x
                  , fcat (map pretty tel)
                  ]
          , nest 2 $ "where"
          ] $$ nest 2 (vcat $ map pretty cs)
    RecordSig _ erased x tel e ->
      sep [ hsep  [ "record"
                  , prettyErased erased (pretty x)
                  , fcat (map pretty tel)
                  ]
          , nest 2 $ hsep
                  [ ":"
                  , pretty e
                  ]
          ]
    Record _ erased x dir tel e cs ->
      pRecord erased x dir tel (Just e) cs
    RecordDef _ x dir tel cs ->
      pRecord defaultErased x dir tel Nothing cs
    RecordDirective r -> pRecordDirective r
    Infix f xs  ->
      pretty f <+> fsep (punctuate comma $ fmap pretty xs)
    Syntax n xs -> "syntax" <+> pretty n <+> "..."
    PatternSyn _ n as p -> "pattern" <+> pretty n <+> fsep (map pretty as)
                             <+> "=" <+> pretty p
    Mutual _ ds     -> namedBlock "mutual" ds
    InterleavedMutual _ ds  -> namedBlock "interleaved mutual" ds
    LoneConstructor _ ds -> namedBlock "constructor" ds
    Abstract _ ds   -> namedBlock "abstract" ds
    Private _ _ ds  -> namedBlock "private" ds
    InstanceB _ ds  -> namedBlock "instance" ds
    Macro _ ds      -> namedBlock "macro" ds
    Postulate _ ds  -> namedBlock "postulate" ds
    Primitive _ ds  -> namedBlock "primitive" ds
    Generalize _ ds -> namedBlock "variable" ds
    Opaque _ ds     -> namedBlock "opaque" ds
    Unfolding _ rs  -> "unfolding" <+> braces (fsep (punctuate semi (pretty <$> rs)))
    Module _ erased x tel ds ->
      hsep [ "module"
           , prettyErased erased (pretty x)
           , fcat (map pretty tel)
           , "where"
           ] $$ nest 2 (vcat $ map pretty ds)
    ModuleMacro _ NotErased{} x (SectionApp _ [] e) DoOpen i
      | isNoName x ->
      sep [ pretty DoOpen
          , nest 2 $ pretty e
          , nest 4 $ pretty i
          ]
    ModuleMacro _ erased x (SectionApp _ tel e) open i ->
      sep [ pretty open <+> "module" <+>
            prettyErased erased (pretty x) <+> fcat (map pretty tel)
          , nest 2 $ "=" <+> pretty e <+> pretty i
          ]
    ModuleMacro _ erased x (RecordModuleInstance _ rec) open i ->
      sep [ pretty open <+> "module" <+> prettyErased erased (pretty x)
          , nest 2 $ "=" <+> pretty rec <+> "{{...}}"
          ]
    Open _ x i  -> hsep [ "open", pretty x, pretty i ]
    Import _ x rn open i   ->
      hsep [ pretty open, "import", pretty x, as rn, pretty i ]
      where
        as Nothing  = empty
        as (Just x) = "as" <+> pretty (asName x)
    UnquoteDecl _ xs t ->
      sep [ "unquoteDecl" <+> fsep (map pretty xs) <+> "=", nest 2 $ pretty t ]
    UnquoteDef _ xs t ->
      sep [ "unquoteDef" <+> fsep (map pretty xs) <+> "=", nest 2 $ pretty t ]
    UnquoteData _ x xs t ->
      sep [ "unquoteData" <+> pretty x <+> fsep (map pretty xs) <+> "=", nest 2 $ pretty t ]
    Pragma pr   -> sep [ "{-#" <+> pretty pr, "#-}" ]
    where
      namedBlock s ds =
          sep [ text s
              , nest 2 $ vcat $ map pretty ds
              ]

pHasEta0 :: HasEta0 -> Doc
pHasEta0 = \case
  YesEta   -> "eta-equality"
  NoEta () -> "no-eta-equality"

pRecordDirective :: RecordDirective -> Doc
pRecordDirective = \case
  Induction ind -> pretty (rangedThing ind)
  Constructor n inst -> hsep [ pInst, "constructor", pretty n ] where
    pInst = case inst of
      InstanceDef{} -> "instance"
      NotInstanceDef{} -> empty
  Eta eta -> pHasEta0 (rangedThing eta)
  PatternOrCopattern{} -> "pattern"

pRecord
  :: Erased
  -> Name
  -> RecordDirectives
  -> [LamBinding]
  -> Maybe Expr
  -> [Declaration]
  -> Doc
pRecord erased x (RecordDirectives ind eta pat con) tel me ds = vcat
    [ sep
      [ hsep  [ "record"
              , prettyErased erased (pretty x)
              , fcat (map pretty tel)
              ]
      , nest 2 $ pType me
      ]
    , nest 2 $ vcat $ concat
      [ pInd
      , pEta
      , pPat
      , pCon
      , map pretty ds
      ]
    ]
  where pType (Just e) = hsep
                [ ":"
                , pretty e
                , "where"
                ]
        pType Nothing  =
                  "where"
        pInd = maybeToList $ pretty . rangedThing <$> ind
        pEta = maybeToList $ eta <&> pHasEta0
        pPat = maybeToList $ "pattern" <$ pat
        -- pEta = caseMaybe eta [] $ \case
        --   YesEta -> [ "eta-equality" ]
        --   NoEta  -> "no-eta-equality" : pPat
        -- pPat = \case
        --   PatternMatching   -> [ "pattern" ]
        --   CopatternMatching -> []
        pCon = maybeToList $ (("constructor" <+>) . pretty) . fst <$> con

instance Pretty OpenShortHand where
    pretty DoOpen = "open"
    pretty DontOpen = empty

instance Pretty Pragma where
    pretty (OptionsPragma _ opts)  = fsep $ map text $ "OPTIONS" : opts
    pretty (BuiltinPragma _ b x)   = hsep [ "BUILTIN", text (rangedThing b), pretty x ]
    pretty (RewritePragma _ _ xs)    =
      hsep [ "REWRITE", hsep $ map pretty xs ]
    pretty (CompilePragma _ b x e) =
      hsep [ "COMPILE", text (rangedThing b), pretty x, text e ]
    pretty (ForeignPragma _ b s) =
      vcat $ text ("FOREIGN " ++ rangedThing b) : map text (lines s)
    pretty (StaticPragma _ i) =
      hsep $ ["STATIC", pretty i]
    pretty (InjectivePragma _ i) =
      hsep $ ["INJECTIVE", pretty i]
    pretty (InlinePragma _ True i) =
      hsep $ ["INLINE", pretty i]
    pretty (NotProjectionLikePragma _ i) =
      hsep $ ["NOT_PROJECTION_LIKE", pretty i]
    pretty (InlinePragma _ False i) =
      hsep $ ["NOINLINE", pretty i]
    pretty (ImpossiblePragma _ strs) =
      hsep $ ["IMPOSSIBLE"] ++ map text strs
    pretty (EtaPragma _ x) =
      hsep $ ["ETA", pretty x]
    pretty (TerminationCheckPragma _ tc) =
      case tc of
        TerminationCheck       -> __IMPOSSIBLE__
        NoTerminationCheck     -> "NO_TERMINATION_CHECK"
        NonTerminating         -> "NON_TERMINATING"
        Terminating            -> "TERMINATING"
        TerminationMeasure _ x -> hsep $ ["MEASURE", pretty x]
    pretty (NoCoverageCheckPragma _) = "NON_COVERING"
    pretty (WarningOnUsage _ nm str) = hsep [ "WARNING_ON_USAGE", pretty nm, text (T.unpack str) ]
    pretty (WarningOnImport _ str)   = hsep [ "WARNING_ON_IMPORT", text (T.unpack str) ]
    pretty (CatchallPragma _) = "CATCHALL"
    pretty (DisplayPragma _ lhs rhs) = "DISPLAY" <+> sep [ pretty lhs <+> "=", nest 2 $ pretty rhs ]
    pretty (NoPositivityCheckPragma _) = "NO_POSITIVITY_CHECK"
    pretty (PolarityPragma _ q occs) =
      hsep ("POLARITY" : pretty q : map pretty occs)
    pretty (NoUniverseCheckPragma _) = "NO_UNIVERSE_CHECK"

instance Pretty Associativity where
  pretty = \case
    LeftAssoc  -> "infixl"
    RightAssoc -> "infixr"
    NonAssoc   -> "infix"

instance Pretty FixityLevel where
  pretty = \case
    Unrelated  -> empty
    Related d  -> text $ toStringWithoutDotZero d

instance Pretty Fixity where
  pretty (Fixity _ level ass) = case level of
    Unrelated  -> empty
    Related{}  -> pretty ass <+> pretty level

instance Pretty NotationPart where
    pretty (IdPart x) = text $ rangedThing x
    pretty HolePart{} = underscore
    pretty VarPart{}  = underscore
    pretty WildPart{} = underscore

    prettyList = hcat . map pretty

instance Pretty Fixity' where
    pretty (Fixity' fix nota _range)
      | null nota = pretty fix
      | otherwise = "syntax" <+> pretty nota

 -- Andreas 2010-09-21: do not print relevance in general, only in function types!
 -- Andreas 2010-09-24: and in record fields
instance Pretty a => Pretty (Arg a) where
  prettyPrec p (Arg ai e) = prettyHiding ai localParens $ prettyPrec p' e
      where p' | visible ai = p
               | otherwise  = 0
            localParens | getOrigin ai == Substitution = parens
                        | otherwise = id

instance Pretty e => Pretty (Named_ e) where
  prettyPrec p (Named nm e)
    | Just s <- bareNameOf nm = mparens (p > 0) $ sep [ text s <+> "=", pretty e ]
    | otherwise               = prettyPrec p e

instance Pretty Pattern where
    prettyList = fsep . map pretty
    pretty = \case
            IdentP _ x      -> pretty x
            AppP p1 p2      -> sep [ pretty p1, nest 2 $ pretty p2 ]
            RawAppP _ ps    -> fsep $ map pretty $ List2.toList ps
            OpAppP _ q _ ps -> fsep $ prettyOpApp (Asp.Name Nothing True) q $ fmap (fmap (fmap (NoPlaceholder Strict.Nothing))) ps
            HiddenP _ p     -> braces' $ pretty p
            InstanceP _ p   -> dbraces $ pretty p
            ParenP _ p      -> parens $ pretty p
            WildP _         -> underscore
            AsP _ x p       -> pretty x <> "@" <> pretty p
            DotP _ p        -> "." <> pretty p
            AbsurdP _       -> "()"
            LitP _ l        -> pretty l
            QuoteP _        -> "quote"
            RecP _ fs       -> sep [ "record", bracesAndSemicolons (map pretty fs) ]
            EqualP _ es     -> sep $ [ parens (sep [pretty e1, "=", pretty e2]) | (e1,e2) <- es ]
            EllipsisP _ mp  -> "..."
            WithP _ p       -> "|" <+> pretty p

prettyOpApp :: forall a .
  Pretty a => Asp.Aspect -> QName -> [NamedArg (MaybePlaceholder a)] -> [Doc]
prettyOpApp asp q es = merge [] $ prOp ms xs es
  where
    -- ms: the module part of the name.
    ms = List1.init (qnameParts q)
    -- xs: the concrete name (alternation of @Id@ and @Hole@)
    xs = case unqualify q of
           Name _ _ xs    -> List1.toList xs
           NoName{}       -> __IMPOSSIBLE__

    prOp :: [Name] -> [NamePart] -> [NamedArg (MaybePlaceholder a)] -> [(Doc, Maybe PositionInName)]
    prOp ms (Hole : xs) (e : es) =
      case namedArg e of
        Placeholder p   -> (qual ms $ pretty e, Just p) : prOp [] xs es
        NoPlaceholder{} -> (pretty e, Nothing) : prOp ms xs es
          -- Module qualifier needs to go on section holes (#3072)
    prOp _  (Hole : _)  []       = __IMPOSSIBLE__
    prOp ms (Id x : xs) es       = ( qual ms $ annotateAspect asp $ pretty $ simpleName x
                                   , Nothing
                                   ) : prOp [] xs es
      -- Qualify the name part with the module.
      -- We then clear @ms@ such that the following name parts will not be qualified.

    prOp _  []       es          = map (\e -> (pretty e, Nothing)) es

    qual ms doc = hcat $ punctuate "." $ map pretty ms ++ [doc]

    -- Section underscores should be printed without surrounding
    -- whitespace. This function takes care of that.
    merge :: [Doc] -> [(Doc, Maybe PositionInName)] -> [Doc]
    merge before []                            = reverse before
    merge before ((d, Nothing) : after)        = merge (d : before) after
    merge before ((d, Just Beginning) : after) = mergeRight before d after
    merge before ((d, Just End)       : after) = case mergeLeft d before of
                                                   (d, bs) -> merge (d : bs) after
    merge before ((d, Just Middle)    : after) = case mergeLeft d before of
                                                   (d, bs) -> mergeRight bs d after

    mergeRight before d after =
      reverse before ++
      case merge [] after of
        []     -> [d]
        a : as -> (d <> a) : as

    mergeLeft d before = case before of
      []     -> (d,      [])
      b : bs -> (b <> d, bs)

instance (Pretty a, Pretty b) => Pretty (ImportDirective' a b) where
    pretty i =
        sep [ public (publicOpen i)
            , pretty $ using i
            , prettyHiding $ hiding i
            , rename $ impRenaming i
            ]
        where
            public Just{}  = "public"
            public Nothing = empty

            prettyHiding [] = empty
            prettyHiding xs = "hiding" <+> parens (fsep $ punctuate ";" $ map pretty xs)

            rename [] = empty
            rename xs = hsep [ "renaming"
                             , parens $ fsep $ punctuate ";" $ map pretty xs
                             ]

instance (Pretty a, Pretty b) => Pretty (Using' a b) where
    pretty UseEverything = empty
    pretty (Using xs)    =
        "using" <+> parens (fsep $ punctuate ";" $ map pretty xs)

instance (Pretty a, Pretty b) => Pretty (Renaming' a b) where
    pretty (Renaming from to mfx _r) = hsep
      [ pretty from
      , "to"
      , maybe empty pretty mfx
      , case to of
          ImportedName a   -> pretty a
          ImportedModule b -> pretty b   -- don't print "module" here
      ]

instance (Pretty a, Pretty b) => Pretty (ImportedName' a b) where
    pretty (ImportedName   a) = pretty a
    pretty (ImportedModule b) = "module" <+> pretty b
