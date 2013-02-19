{-# LANGUAGE CPP, FlexibleInstances #-}
{-# OPTIONS -fno-warn-orphans #-}

{-| Pretty printer for the concrete syntax.
-}
module Agda.Syntax.Concrete.Pretty where

import Data.Char

import qualified Agda.Syntax.Common as Common
import Agda.Syntax.Common hiding (Arg, Dom, NamedArg, ArgInfo)
import Agda.Syntax.Position
import Agda.Syntax.Concrete
import Agda.Syntax.Fixity
import Agda.Syntax.Literal

import Agda.Utils.Pretty
import Agda.Utils.String

#include "../../undefined.h"
import Agda.Utils.Impossible

instance Show Expr	      where show = show . pretty
instance Show Declaration     where show = show . pretty
instance Show Pattern	      where show = show . pretty
instance Show TypedBindings   where show = show . pretty
instance Show LamBinding      where show = show . pretty
instance Show ImportDirective where show = show . pretty
instance Show Pragma	      where show = show . pretty
instance Show RHS	      where show = show . pretty

braces' d = case render d of
  -- Add space to avoid starting a comment
  '-':_ -> braces (text " " <> d)
  _     -> braces d

-- double braces...
dbraces :: Doc -> Doc
dbraces = braces . braces'

arrow  = text "\x2192"
lambda = text "\x03bb"
underscore = text "_"

pHidden :: Pretty a => ArgInfo -> a -> Doc
pHidden i = bracks h . pretty
  where bracks Hidden   = braces'
        bracks Instance = dbraces
        bracks NotHidden= id
        h = argInfoHiding i

pRelevance :: Pretty a => ArgInfo -> a -> Doc
pRelevance i a =
  let d = pretty a
  in  if render d == "_" then d else pretty (argInfoRelevance i) <> d
{-
pRelevance Forced     a = pretty a
pRelevance UnusedArg  a = pretty a
pRelevance Relevant   a = pretty a
pRelevance Irrelevant a =
  let d = pretty a
  in  if render d == "_" then d else text "." <> d
pRelevance NonStrict a =
  let d = pretty a
  in  if render d == "_" then d else text ".." <> d
-}

instance Pretty (ThingWithFixity Name) where
    pretty (ThingWithFixity n _) = pretty n

instance Pretty Name where
    pretty = text . show

instance Pretty QName where
    pretty = text . show

instance Pretty Literal where
    pretty (LitInt _ n)	    = text $ show n
    pretty (LitFloat _ x)   = text $ show x
    pretty (LitString _ s)  = text $ showString' s ""
    pretty (LitChar _ c)    = text $ "'" ++ showChar' c "" ++ "'"
    pretty (LitQName _ x)   = text $ show x

showString' :: String -> ShowS
showString' s =
    foldr (.) id $ [ showString "\"" ] ++ map showChar' s ++ [ showString "\"" ]

showChar' :: Char -> ShowS
showChar' '"'	= showString "\\\""
showChar' c
    | escapeMe c = showLitChar c
    | otherwise	 = showString [c]
    where
	escapeMe c = not (isPrint c) || c == '\\'

instance Pretty Relevance where
  pretty Forced     = empty
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

instance Pretty Expr where
    pretty e =
	case e of
	    Ident x	     -> pretty x
	    Lit l	     -> pretty l
	    QuestionMark _ n -> text "?" <> maybe empty (text . show) n
	    Underscore _ n   -> maybe underscore text n
--	    Underscore _ n   -> underscore <> maybe empty (text . show) n
	    App _ _ _	     ->
		case appView e of
		    AppView e1 args	->
			fsep $ pretty e1 : map pretty args
-- 			sep [ pretty e1
-- 			    , nest 2 $ fsep $ map pretty args
-- 			    ]
	    RawApp _ es   -> fsep $ map pretty es
	    OpApp _ q es -> fsep $ prettyOpApp q es

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
		lambda <+> braces' (fsep $ punctuate (text ";") (map (\(x,y,z) -> prettyClause x y z) pes))
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
		sep [ fsep (map pretty (smashTel tel) ++ [arrow])
		    , pretty e
		    ]
	    Set _   -> text "Set"
	    Prop _  -> text "Prop"
	    SetN _ n	-> text "Set" <> text (showIndex n)
	    Let _ ds e	->
		sep [ text "let" <+> vcat (map pretty ds)
		    , text "in" <+> pretty e
		    ]
	    Paren _ e -> parens $ pretty e
	    As _ x e  -> pretty x <> text "@" <> pretty e
	    Dot _ e   -> text "." <> pretty e
	    Absurd _  -> text "()"
	    Rec _ xs  -> sep (
	        [ text "record {" ] ++
	        punctuate (text ";") (map recPr xs)) <+> text "}"
	    RecUpdate _ e xs ->
	            sep [ text "record" <+> pretty e <+> text "{" ]
	        <+> sep (punctuate (text ";") (map recPr xs))
	        <+> text "}"
            ETel []  -> text "()"
            ETel tel -> fsep $ map pretty tel
            QuoteGoal _ x e -> sep [text "quoteGoal" <+> pretty x <+> text "in",
                                    nest 2 $ pretty e]
            Quote _ -> text "quote"
            QuoteTerm _ -> text "quoteTerm"
	    Unquote _ -> text "unquote"
            -- Andreas, 2011-10-03 print irrelevant things as .(e)
            DontCare e -> text "." <> parens (pretty e)
	where
	  recPr (x, e) = sep [ pretty x <+> text "=" , nest 2 $ pretty e ]

instance Pretty BoundName where
  pretty = pretty . boundName

instance Pretty LamBinding where
    -- TODO guilhem: colors are unused (colored syntax disallowed)
    pretty (DomainFree i x) = pRelevance i $ pHidden i $ pretty x
    pretty (DomainFull b)   = pretty b

instance Pretty TypedBindings where
    pretty (TypedBindings _ a) =
	pRelevance (argInfo a) $ bracks $ pretty $ WithColors (argColors a) $ unArg a
	where
	    bracks = case argHiding a of
			Hidden	    -> braces'
			Instance    -> dbraces
			NotHidden   -> parens


instance Pretty ColoredTypedBinding where
    pretty (WithColors cs  (TNoBind e))    =
	    pretty e <+> pColors "" cs
                -- (x y :{ i j } A) -> ...
    pretty (WithColors cs (TBind _ xs e)) =
	sep [ fsep (map pretty xs)
	    , pColors ":" cs <+> pretty e
	    ]

pColors :: String -> [Color] -> Doc
pColors s [] = text s
pColors s cs = text (s ++ "{") <+> fsep (map pretty cs) <+> text "}"

instance Pretty TypedBinding where
    pretty (TNoBind e) = pretty e
    pretty (TBind _ xs e) =
	sep [ fsep (map pretty xs)
	    , text ":" <+> pretty e
	    ]

smashTel :: Telescope -> Telescope
smashTel (TypedBindings r (Common.Arg i  (TBind r' xs e)) :
          TypedBindings _ (Common.Arg i' (TBind _  ys e')) : tel)
  | show i == show i' && show e == show e' =
    smashTel (TypedBindings r (Common.Arg i (TBind r' (xs ++ ys) e)) : tel)
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
                sep [ pRelevance i $ pretty x <+> pColors ":" (argInfoColors i)
		    , nest 2 $ pretty e
		    ]
            Field x (Common.Arg i e) ->
                sep [ text "field"
                    , nest 2 $ pRelevance i $ pHidden i $
                               TypeSig (i {argInfoRelevance = Relevant}) x e
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
	    Record _ x ind con tel me cs ->
		sep [ hsep  [ text "record"
			    , pretty x
			    , fcat (map pretty tel)
			    ]
		    , nest 2 $ pType me
		    ] $$ nest 2 (vcat $ pInd ++
                                        pCon ++
                                        map pretty cs)
              where pType (Just e) = hsep
			    [ text ":"
			    , pretty e
			    , text "where"
			    ]
                    pType Nothing  =
                              text "where"
                    pInd = maybe [] (\i -> [text $ show i]) ind
                    pCon = maybe [] (\c -> [text "constructor" <+> pretty c]) con
{- ELIMINATED CUT-AND-PASTE CODE
	    Record _ x con tel Nothing cs ->
		sep [ hsep  [ text "record"
			    , pretty x
			    , fcat (map pretty tel)
			    ]
		    , nest 2 $ text "where"
		    ] $$ nest 2 (vcat $ maybe [] (\c -> [text "constructor" <+> pretty c])
                                              con ++
                                        map pretty cs)
-}
            Infix f xs	->
		pretty f <+> (fsep $ punctuate comma $ map pretty xs)
            Syntax n xs -> text "syntax" <+> pretty n <+> text "..."
            PatternSyn _ n as p -> text "pattern" <+> pretty n <+> fsep (map pretty as)
                                     <+> text "=" <+> pretty p
	    Mutual _ ds	    -> namedBlock "mutual" ds
	    Abstract _ ds   -> namedBlock "abstract" ds
	    Private _ ds    -> namedBlock "private" ds
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
	    Open _ x i	-> hsep [ text "open", pretty x, pretty i ]
	    Import _ x rn open i   ->
		hsep [ pretty open, text "import", pretty x, as rn, pretty i ]
		where
		    as Nothing	= empty
		    as (Just x) = text "as" <+> pretty (asName x)
	    Pragma pr	-> sep [ text "{-#" <+> pretty pr, text "#-}" ]
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
    pretty (CompiledPragma _ x hs) =
      hsep [ text "COMPILED", pretty x, text hs ]
    pretty (CompiledTypePragma _ x hs) =
      hsep [ text "COMPILED_TYPE", pretty x, text hs ]
    pretty (CompiledDataPragma _ x hs hcs) =
      hsep $ [text "COMPILED_DATA", pretty x] ++ map text (hs : hcs)
    pretty (CompiledEpicPragma _ x e) =
      hsep [ text "COMPILED_EPIC", pretty x, text e ]
    pretty (CompiledJSPragma _ x e) =
      hsep [ text "COMPILED_JS", pretty x, text e ]
    pretty (StaticPragma _ i) =
      hsep $ [text "STATIC", pretty i]
    pretty (ImportPragma _ i) =
      hsep $ [text "IMPORT", text i]
    pretty (ImpossiblePragma _) =
      hsep $ [text "IMPOSSIBLE"]
    pretty (EtaPragma _ x) =
      hsep $ [text "ETA", pretty x]
    pretty (NoTerminationCheckPragma _) = text "NO_TERMINATION_CHECK"

instance Pretty Fixity where
    pretty (LeftAssoc _ n)  = text "infixl" <+> text (show n)
    pretty (RightAssoc _ n) = text "infixr" <+> text (show n)
    pretty (NonAssoc _ n)   = text "infix" <+> text (show n)

instance Pretty e => Pretty (Arg e) where
 -- Andreas 2010-09-21: do not print relevance in general, only in function types!
 -- Andreas 2010-09-24: and in record fields
    pretty a = -- pRelevance r $
               -- TODO guilhem: print colors
               pHidden (argInfo a) $ unArg a

instance Pretty e => Pretty (Named String e) where
    pretty (Named Nothing e) = pretty e
    pretty (Named (Just s) e) = sep [ text s <+> text "=", pretty e ]

instance Pretty [Pattern] where
    pretty = fsep . map pretty

instance Pretty Pattern where
    pretty p =
	case p of
	    IdentP x      -> pretty x
	    AppP p1 p2    -> sep [ pretty p1, nest 2 $ pretty p2 ]
	    RawAppP _ ps  -> fsep $ map pretty ps
	    OpAppP _ q ps -> fsep $ prettyOpApp q ps
	    HiddenP _ p   -> braces' $ pretty p
	    InstanceP _ p -> dbraces $ pretty p
	    ParenP _ p    -> parens $ pretty p
	    WildP _       -> underscore
	    AsP _ x p     -> pretty x <> text "@" <> pretty p
	    DotP _ p      -> text "." <> pretty p
	    AbsurdP _     -> text "()"
	    LitP l        -> pretty l

prettyOpApp :: Pretty a => QName -> [a] -> [Doc]
prettyOpApp q es = prOp ms xs es
  where
    ms = init (qnameParts q)
    xs = case unqualify q of
           Name _ xs -> xs
           NoName{}  -> __IMPOSSIBLE__
    prOp ms (Hole : xs) (e : es) = pretty e : prOp ms xs es
    prOp _  (Hole : _)  []       = __IMPOSSIBLE__
    prOp ms (Id x : xs) es       = pretty (foldr Qual (QName (Name noRange $ [Id x])) ms) : prOp [] xs es
    prOp _  []	     []          = []
    prOp _  []	     es          = map pretty es

instance Pretty ImportDirective where
    pretty i =
	sep [ public (publicOpen i)
	    , pretty $ usingOrHiding i
	    , rename $ renaming i
	    ]
	where
	    public True  = text "public"
	    public False = empty

	    rename [] = empty
	    rename xs =	hsep [ text "renaming"
			     , parens $ fsep $ punctuate (text ";") $ map pr xs
			     ]

	    pr r = hsep [ pretty (renFrom r), text "to", pretty (renTo r) ]

instance Pretty UsingOrHiding where
    pretty (Hiding [])	= empty
    pretty (Hiding xs)	=
	text "hiding" <+> parens (fsep $ punctuate (text ";") $ map pretty xs)
    pretty (Using xs)	 =
	text "using" <+> parens (fsep $ punctuate (text ";") $ map pretty xs)

instance Pretty ImportedName where
    pretty (ImportedName x)	= pretty x
    pretty (ImportedModule x)	= text "module" <+> pretty x
