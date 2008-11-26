{-# LANGUAGE CPP, FlexibleInstances #-}
{-# OPTIONS -fno-warn-orphans #-}

{-| Pretty printer for the concrete syntax.
-}
module Agda.Syntax.Concrete.Pretty where

import Data.Char

import Agda.Syntax.Common
import Agda.Syntax.Concrete
import Agda.Syntax.Fixity
import Agda.Syntax.Literal

import Agda.Utils.Pretty

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

pHidden :: Pretty a => Hiding -> a -> Doc
pHidden Hidden	    = braces . pretty
pHidden NotHidden   = pretty

instance Pretty Name where
    pretty = text . show

instance Pretty QName where
    pretty = text . show

instance Pretty Literal where
    pretty (LitInt _ n)	    = text $ show n
    pretty (LitFloat _ x)   = text $ show x
    pretty (LitString _ s)  = text $ showString' s ""
    pretty (LitChar _ c)    = text $ "'" ++ showChar' c "" ++ "'"

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

instance Pretty Induction where
  pretty Inductive = text "data"
  pretty CoInductive = text "codata"

instance Pretty Recursion where
  pretty Recursive = text "="
  pretty CoRecursive = text "~"

instance Pretty Expr where
    pretty e =
	case e of
	    Ident x	     -> pretty x
	    Lit l	     -> pretty l
	    QuestionMark _ n -> text "?" <> maybe empty (text . show) n
	    Underscore _ n   -> text "_" <> maybe empty (text . show) n
	    App _ _ _	     ->
		case appView e of
		    AppView e1 args	->
			fsep $ pretty e1 : map pretty args
-- 			sep [ pretty e1
-- 			    , nest 2 $ fsep $ map pretty args
-- 			    ]
	    RawApp _ es   -> fsep $ map pretty es
	    OpApp _ (Name _ xs) es -> fsep $ prOp xs es
		where
		    prOp (Hole : xs) (e : es) = pretty e : prOp xs es
		    prOp (Hole : _)  []       = __IMPOSSIBLE__
		    prOp (Id x : xs) es       = text x : prOp xs es
		    prOp []	     es       = map pretty es
	    OpApp _ (NoName _ _) _ -> __IMPOSSIBLE__

	    WithApp _ e es -> fsep $
	      pretty e : map ((text "|" <+>) . pretty) es

	    HiddenArg _ e -> braces $ pretty e
	    Lam _ bs e ->
		sep [ text "\\" <> fsep (map pretty bs) <+> text "->"
		    , nest 2 $ pretty e
		    ]
            AbsurdLam _ NotHidden -> text "\\ ()"
            AbsurdLam _ Hidden -> text "\\ {}"
	    Fun _ e1 e2 ->
		sep [ pretty e1 <+> text "->"
		    , pretty e2
		    ]
	    Pi tel e ->
		sep [ fsep (map pretty tel ++ [text "->"])
		    , pretty e
		    ]
	    Set _   -> text "Set"
	    Prop _  -> text "Prop"
	    SetN _ n	-> text "Set" <> text (show n)
	    Let _ ds e	->
		sep [ text "let" <+> vcat (map pretty ds)
		    , text "in" <+> pretty e
		    ]
	    Paren _ e -> parens $ pretty e
	    As _ x e  -> pretty x <> text "@" <> pretty e
	    Dot _ e   -> text "." <> pretty e
	    Absurd _  -> text "()"
	    Rec _ xs  -> sep
	      [ text "record"
	      , nest 2 $ braces $ fsep $ punctuate (text ";") $ map pr xs
	      ]
	      where
		pr (x, e) = sep [ pretty x <+> text "="
				, nest 2 $ pretty e
				]

instance Pretty BoundName where
  pretty = pretty . boundName

instance Pretty LamBinding where
    pretty (DomainFree h x) = pHidden h (pretty x)
    pretty (DomainFull b)   = pretty b

instance Pretty TypedBindings where
    pretty (TypedBindings _ h bs) =
	bracks $ fsep $ punctuate semi $ map pretty bs
	where
	    bracks = case h of
			Hidden	    -> braces
			NotHidden   -> parens

instance Pretty TypedBinding where
    pretty (TNoBind e) = pretty e
    pretty (TBind _ xs e) =
	sep [ fsep (punctuate comma $ map pretty xs)
	    , text ":" <+> pretty e
	    ]

instance Pretty RHS where
    pretty (RHS rec e)   = pretty rec <+> pretty e
    pretty AbsurdRHS = empty

instance Pretty WhereClause where
  pretty  NoWhere = empty
  pretty (AnyWhere ds) = vcat [ text "where", nest 2 (vcat $ map pretty ds) ]
  pretty (SomeWhere m ds) =
    vcat [ hsep [ text "module", pretty m, text "where" ]
	 , nest 2 (vcat $ map pretty ds)
	 ]

instance Pretty LHS where
  pretty lhs = case lhs of
    LHS p ps es  -> pr (pretty p) ps es
    Ellipsis _ ps es -> pr (text "...") ps es
    where
      pr d ps es =
        sep [ d
            , nest 2 $ fsep $ map ((text "|" <+>) . pretty) ps
            , nest 2 $ pWith es
            ]
      pWith []	     = empty
      pWith (e : es) = fsep $ (text "with" <+> pretty e)
			    : map ((text "|" <+>) . pretty) es

instance Pretty [Declaration] where
  pretty = vcat . map pretty

instance Pretty Declaration where
    pretty d =
	case d of
	    TypeSig x e	-> sep [ pretty x <+> text ":"
			       , nest 2 $ pretty e
			       ]
            Field x e -> sep [ text "field", nest 2 $ pretty (TypeSig x e) ]
	    FunClause lhs rhs wh ->
		sep [ pretty lhs
		    , nest 2 $ pretty rhs
		    ] $$ nest 2 (pretty wh)
	    Data _ ind x tel e cs ->
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
	    Record _ x tel e cs ->
		sep [ hsep  [ text "record"
			    , pretty x
			    , fcat (map pretty tel)
			    ]
		    , nest 2 $ hsep
			    [ text ":"
			    , pretty e
			    , text "where"
			    ]
		    ] $$ nest 2 (vcat $ map pretty cs)
	    Infix f xs	->
		pretty f <+> (fsep $ punctuate comma $ map pretty xs)
	    
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
	    ModuleMacro _ x tel e open i ->
		sep [ pretty open <+> text "module" <+> pretty x <+> fcat (map pretty tel)
		    , nest 2 $ text "=" <+> pretty e <+> pretty i
		    ]
	    Open _ x i	-> hsep [ text "open", pretty x, pretty i ]
	    Import _ x rn open i   -> 
		hsep [ pretty open, text "import", pretty x, as rn, pretty i ]
		where
		    as Nothing	= empty
		    as (Just x) = text "as" <+> pretty x
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
    pretty (LinePragma _ n f)	  = hsep [ text "LINE", text (show n), text (show f) ]
    pretty (CompiledPragma _ x hs) =
      hsep [ text "COMPILED", pretty x, text hs ]
    pretty (CompiledTypePragma _ x hs) =
      hsep [ text "COMPILED_TYPE", pretty x, text hs ]
    pretty (CompiledDataPragma _ x hs hcs) =
      hsep $ [text "COMPILED_DATA", pretty x] ++ map text (hs : hcs)
    pretty (ImportPragma _ i) =
      hsep $ [text "IMPORT", text i]

instance Pretty Fixity where
    pretty (LeftAssoc _ n)  = text "infixl" <+> text (show n)
    pretty (RightAssoc _ n) = text "infixr" <+> text (show n)
    pretty (NonAssoc _ n)   = text "infix" <+> text (show n)

instance Pretty e => Pretty (Arg e) where
    pretty (Arg h e) = pHidden h e

instance Pretty e => Pretty (Named String e) where
    pretty (Named Nothing e) = pretty e
    pretty (Named (Just s) e) = sep [ text s <+> text "=", pretty e ]

instance Pretty [Pattern] where
    pretty = fsep . map pretty

instance Pretty Pattern where
    pretty p =
	case p of
	    IdentP x	       -> pretty x
	    AppP p1 p2	       -> sep [ pretty p1, nest 2 $ pretty p2 ]
	    RawAppP _ ps       -> fsep $ map pretty ps
	    OpAppP _ (Name _ xs) ps -> fsep $ prOp xs ps
		where
		    prOp (Hole : xs) (e : es) = pretty e : prOp xs es
		    prOp (Hole : _)  []	      = __IMPOSSIBLE__
		    prOp (Id x : xs) es       = text x : prOp xs es
		    prOp []	     []       = []
		    prOp []	     (_ : _)  = __IMPOSSIBLE__
	    OpAppP _ (NoName _ _) _ -> __IMPOSSIBLE__
	    HiddenP _ p	       -> braces $ pretty p
	    ParenP _ p	       -> parens $ pretty p
	    WildP _	       -> text "_"
	    AsP _ x p	       -> pretty x <> text "@" <> pretty p
	    DotP _ p	       -> text "." <> pretty p
	    AbsurdP _	       -> text "()"
	    LitP l	       -> pretty l

instance Pretty ImportDirective where
    pretty i =
	cat [ public (publicOpen i)
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

	    pr (x,y) = hsep [ pretty x, text "to", pretty y ]

instance Pretty UsingOrHiding where
    pretty (Hiding [])	= empty
    pretty (Hiding xs)	=
	text "hiding" <+> parens (fsep $ punctuate (text ";") $ map pretty xs)
    pretty (Using xs)	 =
	text "using" <+> parens (fsep $ punctuate (text ";") $ map pretty xs)

instance Pretty ImportedName where
    pretty (ImportedName x)	= pretty x
    pretty (ImportedModule x)	= text "module" <+> pretty x

