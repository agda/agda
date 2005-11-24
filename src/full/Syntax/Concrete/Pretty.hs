{-# OPTIONS -cpp -fno-warn-orphans #-}

{-| Pretty printer for the concrete syntax.
-}
module Syntax.Concrete.Pretty where

import Data.Char

import Syntax.Common
import Syntax.Concrete

import Utils.Pretty
import Utils.Unicode

#include "../../undefined.h"

instance Show Expr where	    show = show . pretty
instance Show Declaration where    show = show . pretty

pHidden :: Pretty a => Hiding -> a -> Doc
pHidden Hidden	    = braces . pretty
pHidden NotHidden   = pretty

isOpChar c = not $ isAlpha c || isUnicodeId c

name :: String -> Doc
name s@(c:_)
    | isOpChar c    = parens $ text s
    | otherwise	    = text s
name _ = __IMPOSSIBLE__

op :: String -> Doc
op s@(c:_)
    | isOpChar c    = text s
    | otherwise	    = text "`" <> text s <> text "`"
op _ = __IMPOSSIBLE__

prettyOp, prettyId, prettyName :: Show a => a -> Doc
prettyId    = name . show
prettyOp    = op   . show
prettyName  = text . show

instance Pretty Literal where
    pretty (LitInt _ n)	    = text $ show n
    pretty (LitFloat _ x)   = text $ show x
    pretty (LitString _ s)  = text $ show s
    pretty (LitChar _ c)    = text $ show c

instance Pretty Expr where
    pretty e =
	case e of
	    Ident x	    -> prettyId x
	    Lit l	    -> pretty l
	    QuestionMark _  -> text "?"
	    Underscore _    -> text "_"
	    App _ _ _ _	    ->
		case appView e of
		    (e1, args)	->
			sep [ pretty e1
			    , nest 2 $ fsep $ map (uncurry pHidden) args
			    ]
	    InfixApp e1 op e2 ->
		sep [ pretty e1
		    , prettyOp op <+> pretty e2
		    ]
	    Lam _ bs e ->
		sep [ text "\\" <> fsep (map pretty bs) <+> text "->"
		    , nest 2 $ pretty e
		    ]
	    Fun _ h e1 e2 ->
		sep [ pHidden h e1 <+> text "->"
		    , pretty e2
		    ]
	    Pi b e ->
		sep [ pretty b <+> text "->"
		    , pretty e
		    ]
	    Set _   -> text "Set"
	    Prop _  -> text "Prop"
	    SetN _ n	-> text "Set" <> text (show n)
	    Let _ ds e	->
		sep [ text "let" <+> vcat (map pretty ds)
		    , text "in" <+> pretty e
		    ]
	    Paren _ e	-> parens $ pretty e

instance Pretty LamBinding where
    pretty (DomainFree h x) = pHidden h (prettyId x)
    pretty (DomainFull b)   = pretty b

instance Pretty TypedBinding where
    pretty (TypedBinding _ h xs e) =
	bracks $ sep [ fsep (punctuate comma $ map prettyId xs)
		     , text ":" <+> pretty e
		     ]
	where
	    bracks = case h of
			Hidden	    -> braces
			NotHidden   -> parens

instance Pretty Declaration where
    pretty d =
	case d of
	    TypeSig x e	-> sep [ prettyId x <+> text ":"
			       , nest 2 $ pretty e
			       ]
	    FunClause lhs rhs wh ->
		sep [ pretty lhs <+> text "="
		    , nest 2 $ pretty rhs
		    ] $$ nest 2 pwh
		where
		    pwh | null wh   = empty
			| otherwise =
			    vcat [ text "where"
				 , nest 2 $ vcat $ map pretty wh
				 ]
	    Data _ x tel e cs ->
		sep [ hsep  [ text "data"
			    , prettyId x
			    , fcat (map pretty tel)
			    ]
		    , nest 2 $ hsep
			    [ text ":"
			    , pretty e
			    , text "where"
			    ]
		    ] $$ nest 2 (vcat $ map pretty cs)
	    Infix f xs	->
		pretty f <+> (fsep $ punctuate comma $ map prettyOp xs)
	    
	    Mutual _ ds	    -> namedBlock "mutual" ds
	    Abstract _ ds   -> namedBlock "abstract" ds
	    Private _ ds    -> namedBlock "private" ds
	    Postulate _ ds  -> namedBlock "postulate" ds
	    Module _ x tel ds ->
		hsep [ text "module"
		     , prettyId x
		     , fcat (map pretty tel)
		     , text "where"
		     ] $$ nest 2 (vcat $ map pretty ds)
	    ModuleMacro _ x tel e i ->
		sep [ text "module" <+> prettyId x <+> fcat (map pretty tel)
		    , nest 2 $ text "=" <+> pretty e <> pretty i
		    ]
	    Open _ x i	-> text "open" <+> prettyId x <> pretty i
	    Import _ x rn i   -> text "import" <+> prettyId x <+> as rn <> pretty i
		where
		    as Nothing	= empty
		    as (Just x) = text "as" <+> prettyName x
	where
	    namedBlock s ds =
		sep [ text s
		    , nest 2 $ vcat $ map pretty ds
		    ]

instance Pretty Fixity where
    pretty (LeftAssoc _ n)  = text "infixl" <+> text (show n)
    pretty (RightAssoc _ n) = text "infixr" <+> text (show n)
    pretty (NonAssoc _ n)   = text "infix" <+> text (show n)

instance Pretty LHS where
    pretty (LHS _ PrefixDef x es) =
	sep [ prettyId x, nest 2 $ fsep $ map pretty es ]
    pretty (LHS _ InfixDef x (e1:e2:es)) =
	sep [ par $ sep [ pretty e1 <+> prettyOp x
			, nest 2  $ pretty e2
			]
	    , nest 2 $ fsep $ map pretty es
	    ]
	where
	    par | null es   = id
		| otherwise = parens
    pretty _ = __IMPOSSIBLE__

instance Pretty Argument where
    pretty (Argument h p) = pHidden h p

instance Pretty Pattern where
    pretty p =
	case p of
	    IdentP x		-> prettyId x
	    AppP h p1 p2	-> sep [ pretty p1, nest 2 $ pHidden h p2 ]
	    InfixAppP p1 op p2	-> sep [ pretty p1
				       , prettyOp op <+> pretty p2
				       ]
	    ParenP _ p		-> parens $ pretty p
	    WildP _		-> text "_"

instance Pretty ImportDirective where
    pretty i =
	cat [ pretty $ usingOrHiding i
	    , rename $ renaming i
	    ]
	where
	    rename [] = empty
	    rename xs =	hsep [ comma, text "renaming"
			     , parens $ fsep $ punctuate comma $ map pr xs
			     ]

	    pr (x,y) = hsep [ pretty x, text "to", prettyName y ]

instance Pretty UsingOrHiding where
    pretty (Hiding [])	= empty
    pretty (Hiding xs)	=
	comma <+> text "hiding" <+> parens (fsep $ punctuate comma $ map pretty xs)
    pretty (Using xs)	 =
	comma <+> text "using" <+> parens (fsep $ punctuate comma $ map pretty xs)

instance Pretty ImportedName where
    pretty (ImportedName x)	= prettyName x
    pretty (ImportedModule x)	= text "module" <+> prettyName x

