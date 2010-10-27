{-# OPTIONS_GHC -fglasgow-exts -fallow-undecidable-instances #-}

module Abstract where

import Data.List
import Text.PrettyPrint
import Pretty
import Utils

showName = intercalate "."

-- Scope checked terms ----------------------------------------------------

type Var	= String
type Name	= [String]
type ModuleName = Name

data Decl = Section ModuleName Tel [Decl]
	  | Inst ModuleName ModuleName [Expr]
	  | Defn Name Tel Expr Expr [Decl]
	  | Type Name Expr

type Tel = [(Var, Expr)]

data Expr = Pi Var Expr Expr
	  | Set
	  | App Expr Expr
	  | Lam Var Expr
	  | Var Var
	  | Def Name

section _ [] ds  = ds
section m tel ds = [Section m tel ds]

-- Pretty printing --------------------------------------------------------

prettyName :: Name -> Doc
prettyName = hcat . punctuate (text ".") . map text

instance Show Decl where show = show . pretty
instance Show Expr where show = show . pretty

instance Pretty Decl where
    pretty (Section m tel ds) =
	sep [ hsep [ text "section", prettyName m, fsep (map pretty tel), text "where" ]
	    , nest 2 $ vcat $ map pretty ds
	    ]
    pretty (Inst m1 m2 es) =
	sep [ text "apply" <+> prettyName m1 <+> text "="
	    , nest 2 $ fsep $ prettyName m2 : map (prettyPrec 10) es
	    ]
    pretty (Defn x tel t e wh) =
	sep [ sep [ prettyName x <+> fsep (map pretty tel)
		  , nest 2 $ text ":" <+> pretty t
		  , nest 2 $ text "=" <+> pretty e
		  ]
	    , nest 2 $ prettyWhere wh
	    ]
      where
	prettyWhere [] = empty
	prettyWhere ds = sep [ text "where", nest 2 $ vcat $ map pretty ds ]
    pretty (Type x e) =
	sep [ prettyName x <+> text ":"
	    , nest 2 $ pretty e
	    ]

instance Pretty Expr where
    prettyPrec p e = case e of
	Pi "_" a b -> mparens (p > 0) $
	    sep [ prettyPrec 1 a <+> text "->"
		, pretty b
		]
	Pi x a b -> mparens (p > 0) $
	    sep [ parens (text x <+> text ":" <+> pretty a) <+> text "->"
		, pretty b
		]
	Set -> text "Set"
	Lam x t -> mparens (p > 0) $
	    sep [ text "\\" <> text x <+> text "->"
		, pretty t
		]
	App s t -> mparens (p > 1) $
	    sep [ prettyPrec 1 s, prettyPrec 2 t ]
	Var x -> text x
	Def c -> prettyName c

instance Pretty (Var, Expr) where
    pretty (x, e) = parens $ text x <+> text ":" <+> pretty e
