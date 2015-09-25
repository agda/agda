{-# OPTIONS_GHC -fno-warn-orphans #-}

{-# LANGUAGE CPP #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}

{-| Pretty printer for the concrete syntax.
-}
module Agda.Syntax.Concrete.Pretty where

import Prelude hiding (null)

import Data.Functor
import Data.Maybe

import qualified Agda.Syntax.Common as Common
import Agda.Syntax.Common hiding (Arg, Dom, NamedArg, ArgInfo)
import Agda.Syntax.Concrete
import Agda.Syntax.Fixity
import Agda.Syntax.Notation
import Agda.Syntax.Position

import Agda.Utils.Functor
import Agda.Utils.Null
import Agda.Utils.Pretty
import Agda.Utils.String

#include "undefined.h"
import Agda.Utils.Impossible

instance Show Expr            where show = show . pretty
instance Show Declaration     where show = show . pretty
instance Show Pattern         where show = show . pretty
instance Show TypedBinding    where show = show . pretty
instance Show TypedBindings   where show = show . pretty
instance Show LamBinding      where show = show . pretty
instance Show ImportDirective where show = show . pretty
instance Show Pragma          where show = show . pretty
instance Show RHS             where show = show . pretty

braces' :: Doc -> Doc
braces' d = case render d of
  -- Add space to avoid starting a comment
  '-':_ -> braces (text " " <> d)
  _     -> braces d

-- double braces...
dbraces :: Doc -> Doc
dbraces = braces . braces'

-- Lays out a list of documents [d₁, d₂, …] in the following way:
-- @
--   { d₁
--   ; d₂
--   ⋮
--   }
-- @
-- If the list is empty, then the notation @{}@ is used.

bracesAndSemicolons :: [Doc] -> Doc
bracesAndSemicolons []       = text "{}"
bracesAndSemicolons (d : ds) =
  sep ([text "{" <+> d] ++ map (text ";" <+>) ds ++ [text "}"])

arrow, lambda :: Doc
arrow  = text "\x2192"
lambda = text "\x03bb"

-- | @prettyHiding info visible doc@ puts the correct braces
--   around @doc@ according to info @info@ and returns
--   @visible doc@ if the we deal with a visible thing.
prettyHiding :: LensHiding a => a -> (Doc -> Doc) -> Doc -> Doc
prettyHiding a parens =
  case getHiding a of
    Hidden    -> braces'
    Instance  -> dbraces
    NotHidden -> parens

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
  pretty Forced{}   = empty
  pretty UnusedArg  = empty
  pretty Relevant   = empty
  pretty Irrelevant = text "."
  pretty NonStrict  = text ".."

instance Pretty Induction where
  pretty Inductive = text "data"
  pretty CoInductive = text "codata"

instance Pretty (OpApp Expr) where
  pretty (Ordinary e) = pretty e
  pretty (SyntaxBindingLambda r bs e) = pretty (Lam r bs e)

instance Pretty a => Pretty (MaybePlaceholder a) where
  pretty Placeholder{}     = text "_"
  pretty (NoPlaceholder e) = pretty e

instance Pretty Expr where
    pretty e =
        case e of
            Ident x          -> pretty x
            Lit l            -> pretty l
            QuestionMark _ n -> text "?" <> maybe empty (text . show) n
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
              pretty e : map ((text "|" <+>) . pretty) es

            HiddenArg _ e -> braces' $ pretty e
            InstanceArg _ e -> dbraces $ pretty e
            Lam _ bs e ->
                sep [ lambda <+> fsep (map pretty bs) <+> arrow
                    , nest 2 $ pretty e
                    ]
            AbsurdLam _ NotHidden -> lambda <+> text "()"
            AbsurdLam _ Instance -> lambda <+> text "{{}}"
            AbsurdLam _ Hidden -> lambda <+> text "{}"
            ExtendedLam _ pes ->
              lambda <+> bracesAndSemicolons (map (\(x,y,z) -> prettyClause x y z) pes)
                   where prettyClause lhs rhs wh = sep [ pretty lhs
                                                       , nest 2 $ pretty' rhs
                                                       ] $$ nest 2 (pretty wh)
                         pretty' (RHS e)   = arrow <+> pretty e
                         pretty' AbsurdRHS = empty
            Fun _ e1 e2 ->
                sep [ pretty e1 <+> arrow
                    , pretty e2
                    ]
            Pi tel e ->
                sep [ pretty (Tel $ smashTel tel) <+> arrow
                    , pretty e
                    ]
            Set _   -> text "Set"
            Prop _  -> text "Prop"
            SetN _ n    -> text "Set" <> text (showIndex n)
            Let _ ds e  ->
                sep [ text "let" <+> vcat (map pretty ds)
                    , text "in" <+> pretty e
                    ]
            Paren _ e -> parens $ pretty e
            As _ x e  -> pretty x <> text "@" <> pretty e
            Dot _ e   -> text "." <> pretty e
            Absurd _  -> text "()"
            Rec _ xs  -> sep [text "record", bracesAndSemicolons (map pretty xs)]
            RecUpdate _ e xs ->
              sep [text "record" <+> pretty e, bracesAndSemicolons (map pretty xs)]
            ETel []  -> text "()"
            ETel tel -> fsep $ map pretty tel
            QuoteGoal _ x e -> sep [text "quoteGoal" <+> pretty x <+> text "in",
                                    nest 2 $ pretty e]
            QuoteContext _ -> text "quoteContext"
            Quote _ -> text "quote"
            QuoteTerm _ -> text "quoteTerm"
            Unquote _ -> text "unquote"
            Tactic _ t es ->
              sep [ text "tactic" <+> pretty t
                  , fsep [ text "|" <+> pretty e | e <- es ]
                  ]
            -- Andreas, 2011-10-03 print irrelevant things as .(e)
            DontCare e -> text "." <> parens (pretty e)
            Equal _ a b -> pretty a <+> text "=" <+> pretty b

instance (Pretty a, Pretty b) => Pretty (Either a b) where
  pretty = either pretty pretty

instance Pretty a => Pretty (FieldAssignment' a) where
  pretty (FieldAssignment x e) = sep [ pretty x <+> text "=" , nest 2 $ pretty e ]

instance Pretty ModuleAssignment where
  pretty (ModuleAssignment m es i) = (fsep $ pretty m : map pretty es) <+> pretty i

instance Pretty BoundName where
  pretty BName{ boundName = x, boundLabel = l }
    | x == l    = pretty x
    | otherwise = pretty l <+> text "=" <+> pretty x

instance Pretty LamBinding where
    -- TODO guilhem: colors are unused (colored syntax disallowed)
    pretty (DomainFree i x) = prettyRelevance i $ prettyHiding i id $ pretty x
    pretty (DomainFull b)   = pretty b

instance Pretty TypedBindings where
  pretty (TypedBindings _ a) = prettyRelevance a $ prettyHiding a p $
    pretty $ WithColors (argColors a) $ unArg a
      where
        p | isUnderscore (unArg a) = id
          | otherwise        = parens

        isUnderscore (TBind _ _ (Underscore _ Nothing)) = True
        isUnderscore _ = False

newtype Tel = Tel Telescope

instance Pretty Tel where
    pretty (Tel tel)
      | any isMeta tel = text "∀" <+> fsep (map pretty tel)
      | otherwise      = fsep (map pretty tel)
      where
        isMeta (TypedBindings _ (Common.Arg _ (TBind _ _ (Underscore _ Nothing)))) = True
        isMeta _ = False


instance Pretty ColoredTypedBinding where
                -- (x y :{ i j } A) -> ...
    pretty (WithColors [] (TBind _ xs (Underscore _ Nothing))) =
        fsep (map pretty xs)
    pretty (WithColors [] (TLet _ ds)) =
        text "let" <+> vcat (map pretty ds)
    pretty (WithColors _ (TLet _ _)) = __IMPOSSIBLE__
    pretty (WithColors cs (TBind _ xs e)) =
        sep [ fsep (map pretty xs)
            , pColors ":" cs <+> pretty e
            ]

pColors :: String -> [Color] -> Doc
pColors s [] = text s
pColors s cs = text (s ++ "{") <+> fsep (map pretty cs) <+> text "}"

instance Pretty TypedBinding where
    pretty (TBind _ xs e) =
        sep [ fsep (map pretty xs)
            , text ":" <+> pretty e
            ]
    pretty (TLet _ ds) =
        text "let" <+> vcat (map pretty ds)

smashTel :: Telescope -> Telescope
smashTel (TypedBindings r (Common.Arg i  (TBind r' xs e)) :
          TypedBindings _ (Common.Arg i' (TBind _  ys e')) : tel)
  | show i == show i' && show e == show e' && all (isUnnamed . dget) (xs ++ ys) =
    smashTel (TypedBindings r (Common.Arg i (TBind r' (xs ++ ys) e)) : tel)
  where
    isUnnamed x = boundLabel x == boundName x
smashTel (b : tel) = b : smashTel tel
smashTel [] = []


instance Pretty RHS where
    pretty (RHS e)   = text "=" <+> pretty e
    pretty AbsurdRHS = empty

instance Show WhereClause where show = show . pretty
instance Pretty WhereClause where
  pretty  NoWhere = empty
  pretty (AnyWhere [Module _ x [] ds]) | isNoName (unqualify x)
                       = vcat [ text "where", nest 2 (vcat $ map pretty ds) ]
  pretty (AnyWhere ds) = vcat [ text "where", nest 2 (vcat $ map pretty ds) ]
  pretty (SomeWhere m ds) =
    vcat [ hsep [ text "module", pretty m, text "where" ]
         , nest 2 (vcat $ map pretty ds)
         ]

instance Show LHS where show = show . pretty
instance Pretty LHS where
  pretty lhs = case lhs of
    LHS p ps eqs es  -> pr (pretty p) ps eqs es
    Ellipsis _ ps eqs es -> pr (text "...") ps eqs es
    where
      pr d ps eqs es =
        sep [ d
            , nest 2 $ fsep $ map ((text "|" <+>) . pretty) ps
            , nest 2 $ pThing "rewrite" eqs
            , nest 2 $ pThing "with" es
            ]
      pThing thing []       = empty
      pThing thing (e : es) = fsep $ (text thing <+> pretty e)
                                   : map ((text "|" <+>) . pretty) es

instance Show LHSCore where show = show . pretty
instance Pretty LHSCore where
  pretty (LHSHead f ps) = sep $ pretty f : map (parens . pretty) ps
  pretty (LHSProj d ps lhscore ps') = sep $
    pretty d : map (parens . pretty) ps ++
    parens (pretty lhscore) : map (parens . pretty) ps'

instance Pretty [Declaration] where
  pretty = vcat . map pretty

instance Show ModuleApplication where show = show . pretty
instance Pretty ModuleApplication where
  pretty (SectionApp _ bs e) = fsep (map pretty bs) <+> text "=" <+> pretty e
  pretty (RecordModuleIFS _ rec) = text "=" <+> pretty rec <+> text "{{...}}"

instance Pretty Declaration where
    pretty d =
        case d of
            TypeSig i x e ->
                sep [ prettyRelevance i $ pretty x <+> pColors ":" (argInfoColors i)
                    , nest 2 $ pretty e
                    ]
            Field x (Common.Arg i e) ->
                sep [ text "field"
                    , nest 2 $ prettyRelevance i $ prettyHiding i id $
                        pretty $ TypeSig (i {argInfoRelevance = Relevant}) x e
                    ]
            FunClause lhs rhs wh ->
                sep [ pretty lhs
                    , nest 2 $ pretty rhs
                    ] $$ nest 2 (pretty wh)
            DataSig _ ind x tel e ->
                sep [ hsep  [ pretty ind
                            , pretty x
                            , fcat (map pretty tel)
                            ]
                    , nest 2 $ hsep
                            [ text ":"
                            , pretty e
                            ]
                    ]
            Data _ ind x tel (Just e) cs ->
                sep [ hsep  [ pretty ind
                            , pretty x
                            , fcat (map pretty tel)
                            ]
                    , nest 2 $ hsep
                            [ text ":"
                            , pretty e
                            , text "where"
                            ]
                    ] $$ nest 2 (vcat $ map pretty cs)
            Data _ ind x tel Nothing cs ->
                sep [ hsep  [ pretty ind
                            , pretty x
                            , fcat (map pretty tel)
                            ]
                    , nest 2 $ text "where"
                    ] $$ nest 2 (vcat $ map pretty cs)
            RecordSig _ x tel e ->
                sep [ hsep  [ text "record"
                            , pretty x
                            , fcat (map pretty tel)
                            ]
                    , nest 2 $ hsep
                            [ text ":"
                            , pretty e
                            ]
                    ]
            Record _ x ind eta con tel me cs ->
                sep [ hsep  [ text "record"
                            , pretty x
                            , fcat (map pretty tel)
                            ]
                    , nest 2 $ pType me
                    ] $$ nest 2 (vcat $ pInd ++
                                        pEta ++
                                        pCon ++
                                        map pretty cs)
              where pType (Just e) = hsep
                            [ text ":"
                            , pretty e
                            , text "where"
                            ]
                    pType Nothing  =
                              text "where"
                    pInd = maybeToList $ text . show . rangedThing <$> ind
                    pEta = maybeToList $ (\x -> if x then text "eta-equality" else text "no-eta-equality") <$> eta
                    pCon = maybeToList $ (text "constructor" <+>) . pretty <$> fst <$> con
            Infix f xs  ->
                pretty f <+> (fsep $ punctuate comma $ map pretty xs)
            Syntax n xs -> text "syntax" <+> pretty n <+> text "..."
            PatternSyn _ n as p -> text "pattern" <+> pretty n <+> fsep (map pretty as)
                                     <+> text "=" <+> pretty p
            Mutual _ ds     -> namedBlock "mutual" ds
            Abstract _ ds   -> namedBlock "abstract" ds
            Private _ ds    -> namedBlock "private" ds
            InstanceB _ ds  -> namedBlock "instance" ds
            Macro _ ds      -> namedBlock "macro" ds
            Postulate _ ds  -> namedBlock "postulate" ds
            Primitive _ ds  -> namedBlock "primitive" ds
            Module _ x tel ds ->
                hsep [ text "module"
                     , pretty x
                     , fcat (map pretty tel)
                     , text "where"
                     ] $$ nest 2 (vcat $ map pretty ds)
            ModuleMacro _ x (SectionApp _ [] e) DoOpen i | isNoName x ->
                sep [ pretty DoOpen
                    , nest 2 $ pretty e
                    , nest 4 $ pretty i
                    ]
            ModuleMacro _ x (SectionApp _ tel e) open i ->
                sep [ pretty open <+> text "module" <+> pretty x <+> fcat (map pretty tel)
                    , nest 2 $ text "=" <+> pretty e <+> pretty i
                    ]
            ModuleMacro _ x (RecordModuleIFS _ rec) open i ->
                sep [ pretty open <+> text "module" <+> pretty x
                    , nest 2 $ text "=" <+> pretty rec <+> text "{{...}}"
                    ]
            Open _ x i  -> hsep [ text "open", pretty x, pretty i ]
            Import _ x rn open i   ->
                hsep [ pretty open, text "import", pretty x, as rn, pretty i ]
                where
                    as Nothing  = empty
                    as (Just x) = text "as" <+> pretty (asName x)
            UnquoteDecl _ x t ->
              sep [ text "unquoteDecl" <+> pretty x <+> text "=", nest 2 $ pretty t ]
            UnquoteDef _ x t ->
              sep [ text "unquoteDef" <+> pretty x <+> text "=", nest 2 $ pretty t ]
            Pragma pr   -> sep [ text "{-#" <+> pretty pr, text "#-}" ]
        where
            namedBlock s ds =
                sep [ text s
                    , nest 2 $ vcat $ map pretty ds
                    ]

instance Pretty OpenShortHand where
    pretty DoOpen = text "open"
    pretty DontOpen = empty

instance Pretty Pragma where
    pretty (OptionsPragma _ opts) = fsep $ map text $ "OPTIONS" : opts
    pretty (BuiltinPragma _ b x)  = hsep [ text "BUILTIN", text b, pretty x ]
    pretty (RewritePragma _ x)    =
      hsep [ text "REWRITE", pretty x ]
    pretty (CompiledPragma _ x hs) =
      hsep [ text "COMPILED", pretty x, text hs ]
    pretty (CompiledExportPragma _ x hs) =
      hsep [ text "COMPILED_EXPORT", pretty x, text hs ]
    pretty (CompiledTypePragma _ x hs) =
      hsep [ text "COMPILED_TYPE", pretty x, text hs ]
    pretty (CompiledDeclareDataPragma _ x hs) =
      hsep [ text "COMPILED_DECLARE_DATA", pretty x, text hs ]
    pretty (CompiledDataPragma _ x hs hcs) =
      hsep $ [text "COMPILED_DATA", pretty x] ++ map text (hs : hcs)
    pretty (CompiledEpicPragma _ x e) =
      hsep [ text "COMPILED_EPIC", pretty x, text e ]
    pretty (CompiledJSPragma _ x e) =
      hsep [ text "COMPILED_JS", pretty x, text e ]
    pretty (CompiledUHCPragma _ x e) =
      hsep [ text "COMPILED_UHC", pretty x, text e ]
    pretty (CompiledDataUHCPragma _ x crd crcs) =
      hsep $ [ text "COMPILED_DATA_UHC", pretty x] ++ map text (crd : crcs)
    pretty (NoSmashingPragma _ i) =
      hsep $ [text "NO_SMASHING", pretty i]
    pretty (StaticPragma _ i) =
      hsep $ [text "STATIC", pretty i]
    pretty (ImportPragma _ i) =
      hsep $ [text "IMPORT", text i]
    pretty (ImportUHCPragma _ i) =
      hsep $ [text "IMPORT_UHC", text i]
    pretty (ImpossiblePragma _) =
      hsep $ [text "IMPOSSIBLE"]
    pretty (TerminationCheckPragma _ tc) =
      case tc of
        TerminationCheck       -> __IMPOSSIBLE__
        NoTerminationCheck     -> text "NO_TERMINATION_CHECK"
        NonTerminating         -> text "NON_TERMINATING"
        Terminating            -> text "TERMINATING"
        TerminationMeasure _ x -> hsep $ [text "MEASURE", pretty x]
    pretty (CatchallPragma _) = text "CATCHALL"
    pretty (DisplayPragma _ lhs rhs) = text "DISPLAY" <+> sep [ pretty lhs <+> text "=", nest 2 $ pretty rhs ]

instance Pretty Fixity where
    pretty (Fixity _ Unrelated   _)   = __IMPOSSIBLE__
    pretty (Fixity _ (Related n) ass) = text s <+> text (show n)
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

instance Pretty Notation where
    pretty = hcat . map pretty

instance Pretty Fixity' where
    pretty (Fixity' fix nota)
      | nota == noNotation = pretty fix
      | otherwise          = text "syntax" <+> pretty nota

instance Pretty e => Pretty (Arg e) where
 -- Andreas 2010-09-21: do not print relevance in general, only in function types!
 -- Andreas 2010-09-24: and in record fields
    pretty a = -- pRelevance r $
               -- TODO guilhem: print colors
               prettyHiding (argInfo a) id $ pretty $ unArg a

instance Pretty e => Pretty (Named_ e) where
    pretty (Named Nothing e) = pretty e
    pretty (Named (Just s) e) = sep [ text (rawNameToString $ rangedThing s) <+> text "=", pretty e ]

instance Pretty [Pattern] where
    pretty = fsep . map pretty

instance Pretty Pattern where
    pretty p =
        case p of
            IdentP x        -> pretty x
            AppP p1 p2      -> sep [ pretty p1, nest 2 $ pretty p2 ]
            RawAppP _ ps    -> fsep $ map pretty ps
            OpAppP _ q _ ps -> fsep $ prettyOpApp q (fmap (fmap (fmap NoPlaceholder)) ps)
            HiddenP _ p     -> braces' $ pretty p
            InstanceP _ p   -> dbraces $ pretty p
            ParenP _ p      -> parens $ pretty p
            WildP _         -> underscore
            AsP _ x p       -> pretty x <> text "@" <> pretty p
            DotP _ p        -> text "." <> pretty p
            AbsurdP _       -> text "()"
            LitP l          -> pretty l
            QuoteP _        -> text "quote"
            RecP _ fs       -> sep [ text "record", bracesAndSemicolons (map pretty fs) ]

prettyOpApp ::
  Pretty a => QName -> [NamedArg (MaybePlaceholder a)] -> [Doc]
prettyOpApp q es = merge [] $ prOp ms xs es
  where
    ms = init (qnameParts q)
    xs = case unqualify q of
           Name _ xs -> xs
           NoName{}  -> __IMPOSSIBLE__

    prOp ms (Hole : xs) (e : es) = (pretty e, case namedArg e of
                                                Placeholder p -> Just p
                                                _             -> Nothing) :
                                   prOp ms xs es
    prOp _  (Hole : _)  []       = __IMPOSSIBLE__
    prOp ms (Id x : xs) es       = ( pretty (foldr Qual (QName (Name noRange $ [Id x])) ms)
                                   , Nothing
                                   ) : prOp [] xs es
    prOp _  []       []          = []
    prOp _  []       es          = map (\e -> (pretty e, Nothing)) es

    -- Section underscores should be printed without surrounding
    -- whitespace. This function takes care of that.
    merge :: [Doc] -> [(Doc, Maybe Placeholder)] -> [Doc]
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

instance Pretty ImportDirective where
    pretty i =
        sep [ public (publicOpen i)
            , pretty $ using i
            , prettyHiding $ hiding i
            , rename $ renaming i
            ]
        where
            public True  = text "public"
            public False = empty

            prettyHiding [] = empty
            prettyHiding xs = text "hiding" <+> parens (fsep $ punctuate (text ";") $ map pretty xs)

            rename [] = empty
            rename xs = hsep [ text "renaming"
                             , parens $ fsep $ punctuate (text ";") $ map pr xs
                             ]

            pr r = hsep [ pretty (renFrom r), text "to", pretty (renTo r) ]

instance Pretty Using where
    pretty UseEverything = empty
    pretty (Using xs)    =
        text "using" <+> parens (fsep $ punctuate (text ";") $ map pretty xs)

instance Pretty ImportedName where
    pretty (ImportedName x)     = pretty x
    pretty (ImportedModule x)   = text "module" <+> pretty x
