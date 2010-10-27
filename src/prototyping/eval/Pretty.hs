
module Pretty where

import Text.PrettyPrint

import Syntax

instance Show Exp    where show = show . pretty
instance Show Clause where show = show . pretty
instance Show Pat    where show = show . pretty

allNames = tail names
    where names = "" : [ s ++ [c] | s <- names, c <- ['a'..'z'] ]

parens' d = cat [ text "(" <> d, text ")" ]

mparen True  = parens'
mparen False = id

class Pretty a where
    pretty   :: a -> Doc
    prettyP  :: Int -> [Name] -> [Name] -> a -> Doc
    prettyPC :: Int -> [Name] -> [Name] -> a -> ([Name] -> [Name] -> Doc -> b) -> b

    pretty = prettyP 0 allNames []
    prettyP _ _ _ = pretty
    prettyPC p fresh used x ret = ret fresh used (prettyP p fresh used x)

prettyPCs :: Pretty a => Int -> [Name] -> [Name] -> [a] -> ([Name] -> [Name] -> [Doc] -> b) -> b
prettyPCs p fresh used [] ret = ret fresh used []
prettyPCs p fresh used (x : xs) ret =
    prettyPC  p fresh used x  $ \fresh used d  ->
    prettyPCs p fresh used xs $ \fresh used ds ->
    ret fresh used (d : ds)

data V = V

instance Pretty V where
    prettyPC _ (x : fresh) used V ret = ret fresh (x : used) $ text x

instance Pretty Pat where
    prettyPC p fresh used pat ret = case pat of
	ConP c []   -> ret fresh used $ text c
	ConP c ps   -> prettyPCs 2 fresh used ps $ \fresh used ds ->
	    ret fresh used $
	    mparen (p > 1) $
	    fsep $ text c : ds
	WildP	    -> ret fresh used $ text "_"
	VarP	    -> prettyPC p fresh used V ret

instance Pretty Exp where
    prettyP p fresh used v = case v of
	Var n   -> text $ used !!! n
	Con c   -> text c
	Def c	-> text c
	_	    -> case lamView v of
	    Lams n v -> prettyPCs 0 fresh used (replicate n V) $ \fresh used xs ->
		mparen (p > 0) $
		sep [ text "\\" <> fsep xs <> text "."
		    , nest 2 $ prettyP 0 fresh used v
		    ]
	    _	-> case appView v of
		Apps u vs -> mparen (p > 1) $
		    fsep $ prettyP 1 fresh used u
			 : map (prettyP 2 fresh used) vs
	where
	    xs !!! n
		| length xs <= n = "BAD@" ++ show n
		| otherwise	 = xs !! n

instance Pretty Clause where
    pretty (Clause ps v) = prettyPCs 2 allNames [] ps $ \fresh used ps ->
	sep [ fsep ps <+> text "="
	    , nest 2 $ prettyP 0 fresh used v
	    ]
