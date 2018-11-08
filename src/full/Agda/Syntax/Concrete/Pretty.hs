{-# OPTIONS_GHC -fno-warn-orphans #-}

{-# LANGUAGE CPP #-}

{-| Pretty printer for the concrete syntax.
-}
module Agda.Syntax.Concrete.Pretty where

#if MIN_VERSION_base(4,11,0)
import Prelude hiding ( (<>), null )
#else
import Prelude hiding ( null )
#endif

import Data.IORef
import Data.Functor
import Data.Maybe
import qualified Data.Strict.Maybe as Strict

import Agda.Syntax.Common
import Agda.Syntax.Concrete
import Agda.Syntax.Fixity
import Agda.Syntax.Notation
import Agda.Syntax.Position

import Agda.TypeChecking.Positivity.Occurrence

import Agda.Interaction.Options.IORefs (UnicodeOrAscii(..), unicodeOrAscii)

import Agda.Utils.Function
import Agda.Utils.Functor
import Agda.Utils.Null
import Agda.Utils.Pretty
import Agda.Utils.String

#include "undefined.h"
import Agda.Utils.Impossible

import qualified System.IO.Unsafe as UNSAFE (unsafePerformIO)

-- Andreas, 2017-10-02, TODO: restore Show to its original purpose
--
-- deriving instance Show Expr
-- deriving instance (Show a) => Show (OpApp a)
-- deriving instance Show Declaration
-- deriving instance Show Pattern
-- deriving instance Show TypedBinding
-- deriving instance Show TypedBindings
-- deriving instance Show LamBinding
-- deriving instance Show ModuleAssignment
-- deriving instance (Show a, Show b) => Show (ImportDirective' a b)
-- deriving instance (Show a, Show b) => Show (Using' a b)
-- deriving instance (Show a, Show b) => Show (Renaming' a b)
-- deriving instance Show Pragma
-- deriving instance Show RHS
-- deriving instance Show LHS
-- deriving instance Show LHSCore
-- deriving instance Show WhereClause
-- deriving instance Show ModuleApplication

instance Show Expr            where show = show . pretty
instance Show Declaration     where show = show . pretty
instance Show Pattern         where show = show . pretty
instance Show TypedBinding    where show = show . pretty
instance Show TypedBindings   where show = show . pretty
instance Show LamBinding      where show = show . pretty
instance (Pretty a, Pretty b) => Show (ImportDirective' a b)
                              where show = show . pretty
instance Show Pragma          where show = show . pretty
instance Show RHS             where show = show . pretty
instance Show LHS where show = show . pretty
instance Show LHSCore where show = show . pretty
instance Show WhereClause where show = show . pretty
instance Show ModuleApplication where show = show . pretty


-- | Picking the appropriate set of special characters depending on
-- whether we are allowed to use unicode or have to limit ourselves
-- to ascii.

data SpecialCharacters = SpecialCharacters
  { _dbraces :: Doc -> Doc
  , _lambda  :: Doc
  , _arrow   :: Doc
  , _forallQ :: Doc
  }

{-# NOINLINE specialCharacters #-}
specialCharacters :: SpecialCharacters
specialCharacters =
  let opt = UNSAFE.unsafePerformIO (readIORef unicodeOrAscii) in
  case opt of
    UnicodeOk -> SpecialCharacters { _dbraces = (("\x2983 " <>) . (<> " \x2984"))
                                   , _lambda  = "\x03bb"
                                   , _arrow   = "\x2192"
                                   , _forallQ = "\x2200"
                                   }
    AsciiOnly -> SpecialCharacters { _dbraces = braces . braces'
                                   , _lambda  = "\\"
                                   , _arrow   = "->"
                                   , _forallQ = "forall"
                                   }

braces' :: Doc -> Doc
braces' d = ifNull (render d) (braces d) {-else-} $ \ s ->
  braces (spaceIfDash (head s) <> d <> spaceIfDash (last s))
  -- Add space to avoid starting a comment (Ulf, 2010-09-13, #269)
  -- Andreas, 2018-07-21, #3161: Also avoid ending a comment
  where
  spaceIfDash '-' = " "
  spaceIfDash _   = empty

-- double braces...
dbraces :: Doc -> Doc
dbraces = _dbraces specialCharacters

-- forall quantifier
forallQ :: Doc
forallQ = _forallQ specialCharacters

-- Lays out a list of documents [d₁, d₂, …] in the following way:
-- @
--   { d₁
--   ; d₂
--   ⋮
--   }
-- @
-- If the list is empty, then the notation @{}@ is used.

bracesAndSemicolons :: [Doc] -> Doc
bracesAndSemicolons []       = "{}"
bracesAndSemicolons (d : ds) =
  sep (["{" <+> d] ++ map (";" <+>) ds ++ ["}"])

arrow, lambda :: Doc
arrow  = _arrow specialCharacters
lambda = _lambda specialCharacters

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
prettyRelevance a d =
  if render d == "_" then d else pretty (getRelevance a) <> d

instance (Pretty a, Pretty b) => Pretty (a, b) where
    pretty (a, b) = parens $ pretty a <> comma <+> pretty b

instance Pretty (ThingWithFixity Name) where
    pretty (ThingWithFixity n _) = pretty n

instance Pretty a => Pretty (WithHiding a) where
  pretty w = prettyHiding w id $ pretty $ dget w

instance Pretty Relevance where
  pretty Relevant   = empty
  pretty Irrelevant = "."
  pretty NonStrict  = ".."

instance Pretty Induction where
  pretty Inductive = "data"
  pretty CoInductive = "codata"

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
            Lit l            -> pretty l
            QuestionMark _ n -> "?" <> maybe empty (text . show) n
            Underscore _ n   -> maybe underscore text n
--          Underscore _ n   -> underscore <> maybe empty (text . show) n
            App _ _ _        ->
                case appView e of
                    AppView e1 args     ->
                        fsep $ pretty e1 : map pretty args
--                      sep [ pretty e1
--                          , nest 2 $ fsep $ map pretty args
--                          ]
            RawApp _ es    -> fsep $ map pretty es
            OpApp _ q _ es -> fsep $ prettyOpApp q es

            WithApp _ e es -> fsep $
              pretty e : map (("|" <+>) . pretty) es

            HiddenArg _ e -> braces' $ pretty e
            InstanceArg _ e -> dbraces $ pretty e
            Lam _ bs (AbsurdLam _ h) -> lambda <+> fsep (map pretty bs) <+> absurd h
            Lam _ bs e ->
                sep [ lambda <+> fsep (map pretty bs) <+> arrow
                    , nest 2 $ pretty e
                    ]
            AbsurdLam _ h -> lambda <+> absurd h
            ExtendedLam _ pes -> lambda <+> bracesAndSemicolons (map pretty pes)
            Fun _ e1 e2 ->
                sep [ pretty e1 <+> arrow
                    , pretty e2
                    ]
            Pi tel e ->
                sep [ pretty (Tel $ smashTel tel) <+> arrow
                    , pretty e
                    ]
            Set _   -> "Set"
            Prop _  -> "Prop"
            SetN _ n    -> "Set" <> text (showIndex n)
            PropN _ n   -> "Prop" <> text (showIndex n)
            Let _ ds me  ->
                sep [ "let" <+> vcat (map pretty ds)
                    , maybe empty (\ e -> "in" <+> pretty e) me
                    ]
            Paren _ e -> parens $ pretty e
            IdiomBrackets _ e -> "(|" <+> pretty e <+> "|)"
            DoBlock _ ss -> "do" <+> vcat (map pretty ss)
            As _ x e  -> pretty x <> "@" <> pretty e
            Dot _ e   -> "." <> pretty e
            Absurd _  -> "()"
            Rec _ xs  -> sep ["record", bracesAndSemicolons (map pretty xs)]
            RecUpdate _ e xs ->
              sep ["record" <+> pretty e, bracesAndSemicolons (map pretty xs)]
            ETel []  -> "()"
            ETel tel -> fsep $ map pretty tel
            QuoteGoal _ x e -> sep ["quoteGoal" <+> pretty x <+> "in",
                                    nest 2 $ pretty e]
            QuoteContext _ -> "quoteContext"
            Quote _ -> "quote"
            QuoteTerm _ -> "quoteTerm"
            Unquote _ -> "unquote"
            Tactic _ t es ->
              sep [ "tactic" <+> pretty t
                  , fsep [ "|" <+> pretty e | e <- es ]
                  ]
            -- Andreas, 2011-10-03 print irrelevant things as .(e)
            DontCare e -> "." <> parens (pretty e)
            Equal _ a b -> pretty a <+> "=" <+> pretty b
            Ellipsis _  -> "..."
            Generalized e -> pretty e
        where
          absurd NotHidden  = "()"
          absurd Instance{} = "{{}}"
          absurd Hidden     = "{}"

instance (Pretty a, Pretty b) => Pretty (Either a b) where
  pretty = either pretty pretty

instance Pretty a => Pretty (FieldAssignment' a) where
  pretty (FieldAssignment x e) = sep [ pretty x <+> "=" , nest 2 $ pretty e ]

instance Pretty ModuleAssignment where
  pretty (ModuleAssignment m es i) = (fsep $ pretty m : map pretty es) <+> pretty i

instance Pretty LamClause where
  pretty (LamClause lhs rhs wh _) =
    sep [ pretty lhs
        , nest 2 $ pretty' rhs
        ] $$ nest 2 (pretty wh)
    where
      pretty' (RHS e)   = arrow <+> pretty e
      pretty' AbsurdRHS = empty

instance Pretty BoundName where
  pretty BName{ boundName = x, boundLabel = l }
    | x == l    = pretty x
    | otherwise = pretty l <+> "=" <+> pretty x

instance Pretty LamBinding where
    -- TODO guilhem: colors are unused (colored syntax disallowed)
    pretty (DomainFree i x) = prettyRelevance i $ prettyHiding i id $ pretty x
    pretty (DomainFull b)   = pretty b

instance Pretty TypedBindings where
  pretty (TypedBindings _ a) = prettyRelevance a $ prettyHiding a p $
    pretty $ unArg a
      where
        p | isUnderscore (unArg a) = id
          | otherwise        = parens

        isUnderscore (TBind _ _ (Underscore _ Nothing)) = True
        isUnderscore _ = False

newtype Tel = Tel Telescope

instance Pretty Tel where
    pretty (Tel tel)
      | any isMeta tel = forallQ <+> fsep (map pretty tel)
      | otherwise      = fsep (map pretty tel)
      where
        isMeta (TypedBindings _ (Arg _ (TBind _ _ (Underscore _ Nothing)))) = True
        isMeta _ = False


instance Pretty TypedBinding where
    pretty (TBind _ xs (Underscore _ Nothing)) =
      fsep (map pretty xs)
    pretty (TBind _ xs e) =
        sep [ fsep (map pretty xs)
            , ":" <+> pretty e
            ]
    pretty (TLet _ ds) =
        "let" <+> vcat (map pretty ds)

smashTel :: Telescope -> Telescope
smashTel (TypedBindings r (Arg i  (TBind r' xs e)) :
          TypedBindings _ (Arg i' (TBind _  ys e')) : tel)
  | show i == show i' && show e == show e' && all (isUnnamed . dget) (xs ++ ys) =
    smashTel (TypedBindings r (Arg i (TBind r' (xs ++ ys) e)) : tel)
  where
    isUnnamed x = boundLabel x == boundName x
smashTel (b : tel) = b : smashTel tel
smashTel [] = []


instance Pretty RHS where
    pretty (RHS e)   = "=" <+> pretty e
    pretty AbsurdRHS = empty

instance Pretty WhereClause where
  pretty  NoWhere = empty
  pretty (AnyWhere [Module _ x [] ds]) | isNoName (unqualify x)
                       = vcat [ "where", nest 2 (vcat $ map pretty ds) ]
  pretty (AnyWhere ds) = vcat [ "where", nest 2 (vcat $ map pretty ds) ]
  pretty (SomeWhere m a ds) =
    vcat [ hsep $ applyWhen (a == PrivateAccess UserWritten) ("private" :)
             [ "module", pretty m, "where" ]
         , nest 2 (vcat $ map pretty ds)
         ]

instance Pretty LHS where
  pretty lhs = case lhs of
    LHS p eqs es  -> pr (pretty p) eqs es
    where
      pr d eqs es =
        sep [ d
            , nest 2 $ pThing "rewrite" eqs
            , nest 2 $ pThing "with" es
            ]
      pThing thing []       = empty
      pThing thing (e : es) = fsep $ (text thing <+> pretty e)
                                   : map (("|" <+>) . pretty) es

instance Pretty LHSCore where
  pretty (LHSHead f ps) = sep $ pretty f : map (parens . pretty) ps
  pretty (LHSProj d ps lhscore ps') = sep $
    pretty d : map (parens . pretty) ps ++
    parens (pretty lhscore) : map (parens . pretty) ps'
  pretty (LHSWith h wps ps) = if null ps then doc else
      sep $ parens doc : map (parens . pretty) ps
    where
    doc = sep $ pretty h : map (("|" <+>) . pretty) wps

instance Pretty ModuleApplication where
  pretty (SectionApp _ bs e) = fsep (map pretty bs) <+> "=" <+> pretty e
  pretty (RecordModuleIFS _ rec) = "=" <+> pretty rec <+> "{{...}}"

instance Pretty DoStmt where
  pretty (DoBind _ p e cs) =
    ((pretty p <+> "←") <?> pretty e) <?> prCs cs
    where
      prCs [] = empty
      prCs cs = "where" <?> vcat (map pretty cs)
  pretty (DoThen e) = pretty e
  pretty (DoLet _ ds) = "let" <+> vcat (map pretty ds)

instance Pretty Declaration where
    prettyList = vcat . map pretty
    pretty d =
        case d of
            TypeSig i x e ->
                sep [ prettyRelevance i $ pretty x <+> ":"
                    , nest 2 $ pretty e
                    ]
            Field inst x (Arg i e) ->
                sep [ "field"
                    , nest 2 $ mkInst inst $ mkOverlap i $
                      prettyRelevance i $ prettyHiding i id $
                        pretty $ TypeSig (setRelevance Relevant i) x e
                    ]
                where
                  mkInst InstanceDef    d = sep [ "instance", nest 2 d ]
                  mkInst NotInstanceDef d = d

                  mkOverlap i d | isOverlappable i = "overlap" <+> d
                                | otherwise        = d
            FunClause lhs rhs wh _ ->
                sep [ pretty lhs
                    , nest 2 $ pretty rhs
                    ] $$ nest 2 (pretty wh)
            DataSig _ ind x tel e ->
                sep [ hsep  [ pretty ind
                            , pretty x
                            , fcat (map pretty tel)
                            ]
                    , nest 2 $ hsep
                            [ ":"
                            , pretty e
                            ]
                    ]
            Data _ ind x tel (Just e) cs ->
                sep [ hsep  [ pretty ind
                            , pretty x
                            , fcat (map pretty tel)
                            ]
                    , nest 2 $ hsep
                            [ ":"
                            , pretty e
                            , "where"
                            ]
                    ] $$ nest 2 (vcat $ map pretty cs)
            Data _ ind x tel Nothing cs ->
                sep [ hsep  [ pretty ind
                            , pretty x
                            , fcat (map pretty tel)
                            ]
                    , nest 2 $ "where"
                    ] $$ nest 2 (vcat $ map pretty cs)
            RecordSig _ x tel e ->
                sep [ hsep  [ "record"
                            , pretty x
                            , fcat (map pretty tel)
                            ]
                    , nest 2 $ hsep
                            [ ":"
                            , pretty e
                            ]
                    ]
            Record _ x ind eta con tel me cs ->
                sep [ hsep  [ "record"
                            , pretty x
                            , fcat (map pretty tel)
                            ]
                    , nest 2 $ pType me
                    ] $$ nest 2 (vcat $ pInd ++
                                        pEta ++
                                        pCon ++
                                        map pretty cs)
              where pType (Just e) = hsep
                            [ ":"
                            , pretty e
                            , "where"
                            ]
                    pType Nothing  =
                              "where"
                    pInd = maybeToList $ text . show . rangedThing <$> ind
                    pEta = maybeToList $ eta <&> \case
                      YesEta -> "eta-equality"
                      NoEta  -> "no-eta-equality"
                    pCon = maybeToList $ ("constructor" <+>) . pretty <$> fst <$> con
            Infix f xs  ->
                pretty f <+> (fsep $ punctuate comma $ map pretty xs)
            Syntax n xs -> "syntax" <+> pretty n <+> "..."
            PatternSyn _ n as p -> "pattern" <+> pretty n <+> fsep (map pretty as)
                                     <+> "=" <+> pretty p
            Mutual _ ds     -> namedBlock "mutual" ds
            Abstract _ ds   -> namedBlock "abstract" ds
            Private _ _ ds  -> namedBlock "private" ds
            InstanceB _ ds  -> namedBlock "instance" ds
            Macro _ ds      -> namedBlock "macro" ds
            Postulate _ ds  -> namedBlock "postulate" ds
            Primitive _ ds  -> namedBlock "primitive" ds
            Generalize _ ds -> namedBlock "variable" ds
            Module _ x tel ds ->
                hsep [ "module"
                     , pretty x
                     , fcat (map pretty tel)
                     , "where"
                     ] $$ nest 2 (vcat $ map pretty ds)
            ModuleMacro _ x (SectionApp _ [] e) DoOpen i | isNoName x ->
                sep [ pretty DoOpen
                    , nest 2 $ pretty e
                    , nest 4 $ pretty i
                    ]
            ModuleMacro _ x (SectionApp _ tel e) open i ->
                sep [ pretty open <+> "module" <+> pretty x <+> fcat (map pretty tel)
                    , nest 2 $ "=" <+> pretty e <+> pretty i
                    ]
            ModuleMacro _ x (RecordModuleIFS _ rec) open i ->
                sep [ pretty open <+> "module" <+> pretty x
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
            Pragma pr   -> sep [ "{-#" <+> pretty pr, "#-}" ]
        where
            namedBlock s ds =
                sep [ text s
                    , nest 2 $ vcat $ map pretty ds
                    ]

instance Pretty OpenShortHand where
    pretty DoOpen = "open"
    pretty DontOpen = empty

instance Pretty Pragma where
    pretty (OptionsPragma _ opts) = fsep $ map text $ "OPTIONS" : opts
    pretty (BuiltinPragma _ b x _) = hsep [ "BUILTIN", text b, pretty x ]
    pretty (RewritePragma _ xs)    =
      hsep [ "REWRITE", hsep $ map pretty xs ]
    pretty (CompiledPragma _ x hs) =
      hsep [ "COMPILED", pretty x, text hs ]
    pretty (CompiledExportPragma _ x hs) =
      hsep [ "COMPILED_EXPORT", pretty x, text hs ]
    pretty (CompiledTypePragma _ x hs) =
      hsep [ "COMPILED_TYPE", pretty x, text hs ]
    pretty (CompiledDataPragma _ x hs hcs) =
      hsep $ ["COMPILED_DATA", pretty x] ++ map text (hs : hcs)
    pretty (CompiledJSPragma _ x e) =
      hsep [ "COMPILED_JS", pretty x, text e ]
    pretty (CompiledUHCPragma _ x e) =
      hsep [ "COMPILED_UHC", pretty x, text e ]
    pretty (CompiledDataUHCPragma _ x crd crcs) =
      hsep $ [ "COMPILED_DATA_UHC", pretty x] ++ map text (crd : crcs)
    pretty (HaskellCodePragma _ s) =
      vcat ("HASKELL" : map text (lines s))
    pretty (CompilePragma _ b x e) =
      hsep [ "COMPILE", text b, pretty x, text e ]
    pretty (ForeignPragma _ b s) =
      vcat $ text ("FOREIGN " ++ b) : map text (lines s)
    pretty (StaticPragma _ i) =
      hsep $ ["STATIC", pretty i]
    pretty (InjectivePragma _ i) =
      hsep $ ["INJECTIVE", pretty i]
    pretty (InlinePragma _ True i) =
      hsep $ ["INLINE", pretty i]
    pretty (InlinePragma _ False i) =
      hsep $ ["NOINLINE", pretty i]
    pretty (ImportPragma _ i) =
      hsep $ ["IMPORT", text i]
    pretty (ImportUHCPragma _ i) =
      hsep $ ["IMPORT_UHC", text i]
    pretty (ImpossiblePragma _) =
      hsep $ ["IMPOSSIBLE"]
    pretty (EtaPragma _ x) =
      hsep $ ["ETA", pretty x]
    pretty (TerminationCheckPragma _ tc) =
      case tc of
        TerminationCheck       -> __IMPOSSIBLE__
        NoTerminationCheck     -> "NO_TERMINATION_CHECK"
        NonTerminating         -> "NON_TERMINATING"
        Terminating            -> "TERMINATING"
        TerminationMeasure _ x -> hsep $ ["MEASURE", pretty x]
    pretty (WarningOnUsage _ nm str) = hsep [ "WARNING_ON_USAGE", pretty nm, text str ]
    pretty (CatchallPragma _) = "CATCHALL"
    pretty (DisplayPragma _ lhs rhs) = "DISPLAY" <+> sep [ pretty lhs <+> "=", nest 2 $ pretty rhs ]
    pretty (NoPositivityCheckPragma _) = "NO_POSITIVITY_CHECK"
    pretty (PolarityPragma _ q occs) =
      hsep ("POLARITY" : pretty q : map pretty occs)
    pretty (NoUniverseCheckPragma _) = "NO_UNIVERSE_CHECK"

instance Pretty Fixity where
    pretty (Fixity _ Unrelated   _)   = __IMPOSSIBLE__
    pretty (Fixity _ (Related n) ass) = s <+> text (show n)
      where
      s = case ass of
            LeftAssoc  -> "infixl"
            RightAssoc -> "infixr"
            NonAssoc   -> "infix"

instance Pretty GenPart where
    pretty (IdPart x)   = text x
    pretty BindHole{}   = underscore
    pretty NormalHole{} = underscore
    pretty WildHole{}   = underscore

    prettyList = hcat . map pretty

instance Pretty Fixity' where
    pretty (Fixity' fix nota _)
      | nota == noNotation = pretty fix
      | otherwise          = "syntax" <+> pretty nota

 -- Andreas 2010-09-21: do not print relevance in general, only in function types!
 -- Andreas 2010-09-24: and in record fields
instance Pretty a => Pretty (Arg a) where
  prettyPrec p (Arg ai e) = prettyHiding ai localParens $ prettyPrec p' e
      where p' | visible ai = p
               | otherwise  = 0
            localParens | getOrigin ai == Substitution = parens
                        | otherwise = id

instance Pretty e => Pretty (Named_ e) where
    prettyPrec p (Named Nothing e) = prettyPrec p e
    prettyPrec p (Named (Just s) e) = mparens (p > 0) $ sep [ text (rawNameToString $ rangedThing s) <+> "=", pretty e ]

instance Pretty Pattern where
    prettyList = fsep . map pretty
    pretty = \case
            IdentP x        -> pretty x
            AppP p1 p2      -> sep [ pretty p1, nest 2 $ pretty p2 ]
            RawAppP _ ps    -> fsep $ map pretty ps
            OpAppP _ q _ ps -> fsep $ prettyOpApp q (fmap (fmap (fmap (NoPlaceholder Strict.Nothing))) ps)
            HiddenP _ p     -> braces' $ pretty p
            InstanceP _ p   -> dbraces $ pretty p
            ParenP _ p      -> parens $ pretty p
            WildP _         -> underscore
            AsP _ x p       -> pretty x <> "@" <> pretty p
            DotP _ p        -> "." <> pretty p
            AbsurdP _       -> "()"
            LitP l          -> pretty l
            QuoteP _        -> "quote"
            RecP _ fs       -> sep [ "record", bracesAndSemicolons (map pretty fs) ]
            EqualP _ es     -> sep $ [ parens (sep [pretty e1, "=", pretty e2]) | (e1,e2) <- es ]
            EllipsisP _     -> "..."
            WithP _ p       -> "|" <+> pretty p

prettyOpApp :: forall a .
  Pretty a => QName -> [NamedArg (MaybePlaceholder a)] -> [Doc]
prettyOpApp q es = merge [] $ prOp ms xs es
  where
    -- ms: the module part of the name.
    ms = init (qnameParts q)
    -- xs: the concrete name (alternation of @Id@ and @Hole@)
    xs = case unqualify q of
           Name _ xs -> xs
           NoName{}  -> __IMPOSSIBLE__

    prOp :: [Name] -> [NamePart] -> [NamedArg (MaybePlaceholder a)] -> [(Doc, Maybe PositionInName)]
    prOp ms (Hole : xs) (e : es) =
      case namedArg e of
        Placeholder p   -> (qual ms $ pretty e, Just p) : prOp [] xs es
        NoPlaceholder{} -> (pretty e, Nothing) : prOp ms xs es
          -- Module qualifier needs to go on section holes (#3072)
    prOp _  (Hole : _)  []       = __IMPOSSIBLE__
    prOp ms (Id x : xs) es       = ( qual ms $ pretty $ Name noRange $ [Id x]
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
            public True  = "public"
            public False = empty

            prettyHiding [] = empty
            prettyHiding xs = "hiding" <+> parens (fsep $ punctuate ";" $ map pretty xs)

            rename [] = empty
            rename xs = hsep [ "renaming"
                             , parens $ fsep $ punctuate ";" $ map pr xs
                             ]

            pr r = hsep [ pretty (renFrom r), "to", pretty (renTo r) ]

instance (Pretty a, Pretty b) => Pretty (Using' a b) where
    pretty UseEverything = empty
    pretty (Using xs)    =
        "using" <+> parens (fsep $ punctuate ";" $ map pretty xs)

instance (Pretty a, Pretty b) => Pretty (ImportedName' a b) where
    pretty (ImportedName x)     = pretty x
    pretty (ImportedModule x)   = "module" <+> pretty x
