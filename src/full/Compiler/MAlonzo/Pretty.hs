{-# OPTIONS_GHC -w #-}

-- M.T: Modified Pretty HsExp instance to print parens right.


-----------------------------------------------------------------------------
-- |
-- Module      :  Language.Haskell.Pretty
-- Copyright   :  (c) The GHC Team, Noel Winstanley 1997-2000
-- License     :  BSD-style (see the file libraries/base/LICENSE)
--
-- Maintainer  :  libraries@haskell.org
-- Stability   :  experimental
-- Portability :  portable
--
-- Pretty printer for Haskell.
--
-----------------------------------------------------------------------------

module Compiler.MAlonzo.Pretty (
		-- * Pretty printing
		Pretty,
		prettyPrintStyleMode, prettyPrintWithMode, prettyPrint,
		-- * Pretty-printing styles (from "Text.PrettyPrint.HughesPJ")
		P.Style(..), P.style, P.Mode(..),
		-- * Haskell formatting modes
		PPHsMode(..), Indent, PPLayout(..), defaultMode) where

import Language.Haskell.Syntax

import qualified Text.PrettyPrint as P

infixl 5 $$$

-----------------------------------------------------------------------------

-- | Varieties of layout we can use.
data PPLayout = PPOffsideRule	-- ^ classical layout
	      | PPSemiColon	-- ^ classical layout made explicit
	      | PPInLine	-- ^ inline decls, with newlines between them
	      | PPNoLayout	-- ^ everything on a single line
	      deriving Eq

type Indent = Int

-- | Pretty-printing parameters.
--
-- /Note:/ the 'onsideIndent' must be positive and less than all other indents.
data PPHsMode = PPHsMode {
				-- | indentation of a class or instance
		classIndent :: Indent,
				-- | indentation of a @do@-expression
		doIndent :: Indent,
				-- | indentation of the body of a
				-- @case@ expression
		caseIndent :: Indent,
				-- | indentation of the declarations in a
				-- @let@ expression
		letIndent :: Indent,
				-- | indentation of the declarations in a
				-- @where@ clause
		whereIndent :: Indent,
				-- | indentation added for continuation
				-- lines that would otherwise be offside
		onsideIndent :: Indent,
				-- | blank lines between statements?
		spacing :: Bool,
				-- | Pretty-printing style to use
		layout :: PPLayout,
				-- | add GHC-style @LINE@ pragmas to output?
		linePragmas :: Bool,
				-- | not implemented yet
		comments :: Bool
		}

-- | The default mode: pretty-print using the offside rule and sensible
-- defaults.
defaultMode :: PPHsMode
defaultMode = PPHsMode{
		      classIndent = 8,
		      doIndent = 3,
		      caseIndent = 4,
		      letIndent = 4,
		      whereIndent = 6,
		      onsideIndent = 2,
		      spacing = True,
		      layout = PPOffsideRule,
		      linePragmas = False,
		      comments = True
		      }

-- | Pretty printing monad
newtype DocM s a = DocM (s -> a)

instance Functor (DocM s) where
	 fmap f xs = do x <- xs; return (f x)

instance Monad (DocM s) where
	(>>=) = thenDocM
	(>>) = then_DocM
	return = retDocM

{-# INLINE thenDocM #-}
{-# INLINE then_DocM #-}
{-# INLINE retDocM #-}
{-# INLINE unDocM #-}
{-# INLINE getPPEnv #-}

thenDocM :: DocM s a -> (a -> DocM s b) -> DocM s b
thenDocM m k = DocM $ (\s -> case unDocM m $ s of a -> unDocM (k a) $ s)

then_DocM :: DocM s a -> DocM s b -> DocM s b
then_DocM m k = DocM $ (\s -> case unDocM m $ s of _ -> unDocM k $ s)

retDocM :: a -> DocM s a
retDocM a = DocM (\_s -> a)

unDocM :: DocM s a -> (s -> a)
unDocM (DocM f) = f

-- all this extra stuff, just for this one function.
getPPEnv :: DocM s s
getPPEnv = DocM id

-- So that pp code still looks the same
-- this means we lose some generality though

-- | The document type produced by these pretty printers uses a 'PPHsMode'
-- environment.
type Doc = DocM PPHsMode P.Doc

-- | Things that can be pretty-printed, including all the syntactic objects
-- in "Language.Haskell.Syntax".
class Pretty a where
	-- | Pretty-print something in isolation.
	pretty :: a -> Doc
	-- | Pretty-print something in a precedence context.
	prettyPrec :: Int -> a -> Doc
	pretty = prettyPrec 0
	prettyPrec _ = pretty

-- The pretty printing combinators

empty :: Doc
empty = return P.empty

nest :: Int -> Doc -> Doc
nest i m = m >>= return . P.nest i


-- Literals

text, ptext :: String -> Doc
text = return . P.text
ptext = return . P.text

char :: Char -> Doc
char = return . P.char

int :: Int -> Doc
int = return . P.int

integer :: Integer -> Doc
integer = return . P.integer

float :: Float -> Doc
float = return . P.float

double :: Double -> Doc
double = return . P.double

rational :: Rational -> Doc
rational = return . P.rational

-- Simple Combining Forms

parens, brackets, braces,quotes,doubleQuotes :: Doc -> Doc
parens d = d >>= return . P.parens
brackets d = d >>= return . P.brackets
braces d = d >>= return . P.braces
quotes d = d >>= return . P.quotes
doubleQuotes d = d >>= return . P.doubleQuotes

parensIf :: Bool -> Doc -> Doc
parensIf True = parens
parensIf False = id

-- Constants

semi,comma,colon,space,equals :: Doc
semi = return P.semi
comma = return P.comma
colon = return P.colon
space = return P.space
equals = return P.equals

lparen,rparen,lbrack,rbrack,lbrace,rbrace :: Doc
lparen = return  P.lparen
rparen = return  P.rparen
lbrack = return  P.lbrack
rbrack = return  P.rbrack
lbrace = return  P.lbrace
rbrace = return  P.rbrace

-- Combinators

(<>),(<+>),($$),($+$) :: Doc -> Doc -> Doc
aM <> bM = do{a<-aM;b<-bM;return (a P.<> b)}
aM <+> bM = do{a<-aM;b<-bM;return (a P.<+> b)}
aM $$ bM = do{a<-aM;b<-bM;return (a P.$$ b)}
aM $+$ bM = do{a<-aM;b<-bM;return (a P.$+$ b)}

hcat,hsep,vcat,sep,cat,fsep,fcat :: [Doc] -> Doc
hcat dl = sequence dl >>= return . P.hcat
hsep dl = sequence dl >>= return . P.hsep
vcat dl = sequence dl >>= return . P.vcat
sep dl = sequence dl >>= return . P.sep
cat dl = sequence dl >>= return . P.cat
fsep dl = sequence dl >>= return . P.fsep
fcat dl = sequence dl >>= return . P.fcat

-- Some More

hang :: Doc -> Int -> Doc -> Doc
hang dM i rM = do{d<-dM;r<-rM;return $ P.hang d i r}

-- Yuk, had to cut-n-paste this one from Pretty.hs
punctuate :: Doc -> [Doc] -> [Doc]
punctuate _ []     = []
punctuate p (d1:ds) = go d1 ds
                   where
                     go d [] = [d]
                     go d (e:es) = (d <> p) : go e es

-- | render the document with a given style and mode.
renderStyleMode :: P.Style -> PPHsMode -> Doc -> String
renderStyleMode ppStyle ppMode d = P.renderStyle ppStyle . unDocM d $ ppMode

-- | render the document with a given mode.
renderWithMode :: PPHsMode -> Doc -> String
renderWithMode = renderStyleMode P.style

-- | render the document with 'defaultMode'.
render :: Doc -> String
render = renderWithMode defaultMode

-- | pretty-print with a given style and mode.
prettyPrintStyleMode :: Pretty a => P.Style -> PPHsMode -> a -> String
prettyPrintStyleMode ppStyle ppMode = renderStyleMode ppStyle ppMode . pretty

-- | pretty-print with the default style and a given mode.
prettyPrintWithMode :: Pretty a => PPHsMode -> a -> String
prettyPrintWithMode = prettyPrintStyleMode P.style

-- | pretty-print with the default style and 'defaultMode'.
prettyPrint :: Pretty a => a -> String
prettyPrint = prettyPrintWithMode defaultMode

fullRenderWithMode :: PPHsMode -> P.Mode -> Int -> Float ->
		      (P.TextDetails -> a -> a) -> a -> Doc -> a
fullRenderWithMode ppMode m i f fn e mD =
		   P.fullRender m i f fn e $ (unDocM mD) ppMode


fullRender :: P.Mode -> Int -> Float -> (P.TextDetails -> a -> a)
	      -> a -> Doc -> a
fullRender = fullRenderWithMode defaultMode

-------------------------  Pretty-Print a Module --------------------
instance Pretty HsModule where
	pretty (HsModule pos m mbExports imp decls) =
		markLine pos $
		topLevel (ppHsModuleHeader m mbExports)
			 (map pretty imp ++ map pretty decls)

--------------------------  Module Header ------------------------------
ppHsModuleHeader :: Module -> Maybe [HsExportSpec] ->  Doc
ppHsModuleHeader m mbExportList = mySep [
	text "module",
	pretty m,
	maybePP (parenList . map pretty) mbExportList,
	text "where"]

instance Pretty Module where
	pretty (Module modName) = text modName

instance Pretty HsExportSpec where
	pretty (HsEVar name)		    = pretty name
	pretty (HsEAbs name)		    = pretty name
	pretty (HsEThingAll name)	    = pretty name <> text "(..)"
	pretty (HsEThingWith name nameList) =
		pretty name <> (parenList . map pretty $ nameList)
	pretty (HsEModuleContents m)       = text "module" <+> pretty m

instance Pretty HsImportDecl where
	pretty (HsImportDecl pos m qual mbName mbSpecs) =
		markLine pos $
		mySep [text "import",
		       if qual then text "qualified" else empty,
		       pretty m,
		       maybePP (\m' -> text "as" <+> pretty m') mbName,
		       maybePP exports mbSpecs]
	    where
		exports (b,specList) =
			if b then text "hiding" <+> specs else specs
		    where specs = parenList . map pretty $ specList

instance Pretty HsImportSpec where
	pretty (HsIVar name)                = pretty name
	pretty (HsIAbs name)                = pretty name
	pretty (HsIThingAll name)           = pretty name <> text "(..)"
	pretty (HsIThingWith name nameList) =
		pretty name <> (parenList . map pretty $ nameList)

-------------------------  Declarations ------------------------------
instance Pretty HsDecl where
	pretty (HsTypeDecl loc name nameList htype) =
		blankline $
		markLine loc $
		mySep ( [text "type", pretty name]
			++ map pretty nameList
			++ [equals, pretty htype])

	pretty (HsDataDecl loc context name nameList constrList derives) =
		blankline $
		markLine loc $
		mySep ( [text "data", ppHsContext context, pretty name]
			++ map pretty nameList)
			<+> (myVcat (zipWith (<+>) (equals : repeat (char '|'))
						   (map pretty constrList))
			$$$ ppHsDeriving derives)

	pretty (HsNewTypeDecl pos context name nameList constr derives) =
		blankline $
		markLine pos $
		mySep ( [text "newtype", ppHsContext context, pretty name]
			++ map pretty nameList)
			<+> equals <+> (pretty constr $$$ ppHsDeriving derives)

	--m{spacing=False}
	-- special case for empty class declaration
	pretty (HsClassDecl pos context name nameList []) =
		blankline $
		markLine pos $
		mySep ( [text "class", ppHsContext context, pretty name]
			++ map pretty nameList)
	pretty (HsClassDecl pos context name nameList declList) =
		blankline $
		markLine pos $
		mySep ( [text "class", ppHsContext context, pretty name]
			++ map pretty nameList ++ [text "where"])
		$$$ ppBody classIndent (map pretty declList)

	-- m{spacing=False}
	-- special case for empty instance declaration
	pretty (HsInstDecl pos context name args []) =
		blankline $
		markLine pos $
		mySep ( [text "instance", ppHsContext context, pretty name]
			++ map ppHsAType args)
	pretty (HsInstDecl pos context name args declList) =
		blankline $
		markLine pos $
		mySep ( [text "instance", ppHsContext context, pretty name]
			++ map ppHsAType args ++ [text "where"])
		$$$ ppBody classIndent (map pretty declList)

	pretty (HsDefaultDecl pos htypes) =
		blankline $
		markLine pos $
		text "default" <+> parenList (map pretty htypes)

	pretty (HsTypeSig pos nameList qualType) =
		blankline $
		markLine pos $
		mySep ((punctuate comma . map pretty $ nameList)
		      ++ [text "::", pretty qualType])

	pretty (HsForeignImport pos conv safety entity name ty) =
		blankline $
		markLine pos $
		mySep $ [text "foreign", text "import", text conv, pretty safety] ++
			(if null entity then [] else [text (show entity)]) ++
			[pretty name, text "::", pretty ty]

	pretty (HsForeignExport pos conv entity name ty) =
		blankline $
		markLine pos $
		mySep $ [text "foreign", text "export", text conv] ++
			(if null entity then [] else [text (show entity)]) ++
			[pretty name, text "::", pretty ty]

	pretty (HsFunBind matches) =
		ppBindings (map pretty matches)

	pretty (HsPatBind pos pat rhs whereDecls) =
		markLine pos $
		myFsep [pretty pat, pretty rhs] $$$ ppWhere whereDecls

	pretty (HsInfixDecl pos assoc prec opList) =
		blankline $
		markLine pos $
		mySep ([pretty assoc, int prec]
		       ++ (punctuate comma . map pretty $ opList))

instance Pretty HsAssoc where
	pretty HsAssocNone  = text "infix"
	pretty HsAssocLeft  = text "infixl"
	pretty HsAssocRight = text "infixr"

instance Pretty HsSafety where
	pretty HsSafe    = text "safe"
	pretty HsUnsafe  = text "unsafe"

instance Pretty HsMatch where
	pretty (HsMatch pos f ps rhs whereDecls) =
		markLine pos $
		myFsep (lhs ++ [pretty rhs])
		$$$ ppWhere whereDecls
	    where
		lhs = case ps of
			l:r:ps' | isSymbolName f ->
				let hd = [pretty l, ppHsName f, pretty r] in
				if null ps' then hd
				else parens (myFsep hd) : map (prettyPrec 2) ps'
			_ -> pretty f : map (prettyPrec 2) ps

ppWhere :: [HsDecl] -> Doc
ppWhere [] = empty
ppWhere l = nest 2 (text "where" $$$ ppBody whereIndent (map pretty l))

------------------------- Data & Newtype Bodies -------------------------
instance Pretty HsConDecl where
	pretty (HsRecDecl _pos name fieldList) =
		pretty name <> (braceList . map ppField $ fieldList)

	pretty (HsConDecl _pos name@(HsSymbol _) [l, r]) =
		myFsep [prettyPrec prec_btype l, ppHsName name,
			prettyPrec prec_btype r]
	pretty (HsConDecl _pos name typeList) =
		mySep $ ppHsName name : map (prettyPrec prec_atype) typeList

ppField :: ([HsName],HsBangType) -> Doc
ppField (names, ty) =
	myFsepSimple $ (punctuate comma . map pretty $ names) ++
		       [text "::", pretty ty]

instance Pretty HsBangType where
	prettyPrec _ (HsBangedTy ty) = char '!' <> ppHsAType ty
	prettyPrec p (HsUnBangedTy ty) = prettyPrec p ty

ppHsDeriving :: [HsQName] -> Doc
ppHsDeriving []  = empty
ppHsDeriving [d] = text "deriving" <+> ppHsQName d
ppHsDeriving ds  = text "deriving" <+> parenList (map ppHsQName ds)

------------------------- Types -------------------------
instance Pretty HsQualType where
	pretty (HsQualType context htype) =
		myFsep [ppHsContext context, pretty htype]

ppHsBType :: HsType -> Doc
ppHsBType = prettyPrec prec_btype

ppHsAType :: HsType -> Doc
ppHsAType = prettyPrec prec_atype

-- precedences for types
prec_btype, prec_atype :: Int
prec_btype = 1	-- left argument of ->,
		-- or either argument of an infix data constructor
prec_atype = 2	-- argument of type or data constructor, or of a class

instance Pretty HsType where
	prettyPrec p (HsTyFun a b) = parensIf (p > 0) $
		myFsep [ppHsBType a, text "->", pretty b]
	prettyPrec _ (HsTyTuple l) = parenList . map pretty $ l
	prettyPrec p (HsTyApp a b)
		| a == list_tycon = brackets $ pretty b		-- special case
		| otherwise = parensIf (p > prec_btype) $
			myFsep [pretty a, ppHsAType b]
	prettyPrec _ (HsTyVar name) = pretty name
	prettyPrec _ (HsTyCon name) = pretty name

------------------------- Expressions -------------------------
instance Pretty HsRhs where
	pretty (HsUnGuardedRhs e) = equals <+> pretty e
	pretty (HsGuardedRhss guardList) = myVcat . map pretty $ guardList

instance Pretty HsGuardedRhs where
	pretty (HsGuardedRhs _pos guard body) =
		myFsep [char '|', pretty guard, equals, pretty body]

instance Pretty HsLiteral where
	pretty (HsInt i)        = integer i
	pretty (HsChar c)       = text (show c)
	pretty (HsString s)     = text (show s)
	pretty (HsFrac r)       = double (fromRational r)
	-- GHC unboxed literals:
	pretty (HsCharPrim c)   = text (show c)           <> char '#'
	pretty (HsStringPrim s) = text (show s)           <> char '#'
	pretty (HsIntPrim i)    = integer i               <> char '#'
	pretty (HsFloatPrim r)  = float  (fromRational r) <> char '#'
	pretty (HsDoublePrim r) = double (fromRational r) <> text "##"

instance Pretty HsExp where
  prettyPrec p0 e0 = let
        pI i    = parensIf (p0 > i)
        pP i x  = prettyPrec i x
        pP0  x  = pP 0 x
        pP0s xs = map pP0 xs
    in case e0 of
	HsLit l -> pretty l
	-- lambda stuff
	HsInfixApp a op b -> pI 10 $ myFsep [pP 10 a, pretty op, pP 11 b]
	HsNegApp e -> myFsep [char '-', pP 10 e]
	HsApp a b -> pI 10 $ myFsep [pP 10 a, pP 11 b]
	HsLambda _loc expList body -> pI 10 $ myFsep $
		char '\\' : map (pP 10) expList ++ [text "->", pP 0 $ body]
	-- keywords
	HsLet expList letBody -> pI 10 $
		myFsep [text "let" <+> ppBody letIndent (pP0s expList),
			text "in", pP 0 letBody]
	HsIf cond thenexp elsexp -> pI 10 $
		myFsep [text "if", pP 0 cond,
			text "then", pP 0 thenexp,
			text "else", pP 0 elsexp]
	HsCase cond altList -> pI 10 $
		myFsep [text "case", pP 0 cond, text "of"]
		$$$ ppBody caseIndent (pP0s altList)
	HsDo stmtList -> pI 10 $
		text "do" $$$ ppBody doIndent (pP0s stmtList)
	-- Constructors & Vars
	HsVar name -> pretty name
	HsCon name -> pretty name
	HsTuple expList -> parenList . pP0s $ expList
	-- weird stuff
	HsParen e -> parens . pretty $ e
	HsLeftSection e op -> parens (pP 10 e <+> pretty op)
	HsRightSection op e -> parens (pretty op <+> pP 10 e)
	HsRecConstr c fieldList -> 
		pretty c <> (braceList . map pretty $ fieldList)
	HsRecUpdate e fieldList -> 
		pretty e <> (braceList . map pretty $ fieldList)
	-- patterns
	-- special case that would otherwise be buggy
	HsAsPat name (HsIrrPat e) -> 
		myFsep [pretty name <> char '@', char '~' <> pretty e]
	HsAsPat name e -> hcat [pretty name, char '@', pretty e]
	HsWildCard -> char '_'
	HsIrrPat e -> char '~' <> pretty e
	-- Lists
	HsList list -> 
		bracketList . punctuate comma . map pretty $ list
	HsEnumFrom e -> 
		bracketList [pretty e, text ".."]
	HsEnumFromTo from to -> 
		bracketList [pretty from, text "..", pretty to]
	HsEnumFromThen from thenE -> 
		bracketList [pretty from <> comma, pretty thenE, text ".."]
	HsEnumFromThenTo from thenE to -> 
		bracketList [pretty from <> comma, pretty thenE,
			     text "..", pretty to]
	HsListComp e stmtList -> 
		bracketList ([pretty e, char '|']
			     ++ (punctuate comma . map pretty $ stmtList))
	HsExpTypeSig _pos e ty -> pI 0 $
		myFsep [pretty e, text "::", pretty ty]

------------------------- Patterns -----------------------------

instance Pretty HsPat where
	prettyPrec _ (HsPVar name) = pretty name
	prettyPrec _ (HsPLit lit) = pretty lit
	prettyPrec _ (HsPNeg p) = myFsep [char '-', pretty p]
	prettyPrec p (HsPInfixApp a op b) = parensIf (p > 0) $
		myFsep [pretty a, pretty (HsQConOp op), pretty b]
	prettyPrec p (HsPApp n ps) = parensIf (p > 1) $
		myFsep (pretty n : map pretty ps)
	prettyPrec _ (HsPTuple ps) = parenList . map pretty $ ps
	prettyPrec _ (HsPList ps) =
		bracketList . punctuate comma . map pretty $ ps
	prettyPrec _ (HsPParen p) = parens . pretty $ p
	prettyPrec _ (HsPRec c fields) =
		pretty c <> (braceList . map pretty $ fields)
	-- special case that would otherwise be buggy
	prettyPrec _ (HsPAsPat name (HsPIrrPat pat)) =
		myFsep [pretty name <> char '@', char '~' <> pretty pat]
	prettyPrec _ (HsPAsPat name pat) =
		hcat [pretty name, char '@', pretty pat]
	prettyPrec _ HsPWildCard = char '_'
	prettyPrec _ (HsPIrrPat pat) = char '~' <> pretty pat

instance Pretty HsPatField where
	pretty (HsPFieldPat name pat) =
		myFsep [pretty name, equals, pretty pat]

------------------------- Case bodies  -------------------------
instance Pretty HsAlt where
	pretty (HsAlt _pos e gAlts decls) =
		myFsep [pretty e, pretty gAlts] $$$ ppWhere decls

instance Pretty HsGuardedAlts where
	pretty (HsUnGuardedAlt e) = text "->" <+> pretty e
	pretty (HsGuardedAlts altList) = myVcat . map pretty $ altList

instance Pretty HsGuardedAlt where
	pretty (HsGuardedAlt _pos e body) =
		myFsep [char '|', pretty e, text "->", pretty body]

------------------------- Statements in monads & list comprehensions -----
instance Pretty HsStmt where
	pretty (HsGenerator _loc e from) =
		pretty e <+> text "<-" <+> pretty from
	pretty (HsQualifier e) = pretty e
	pretty (HsLetStmt declList) =
		text "let" $$$ ppBody letIndent (map pretty declList)

------------------------- Record updates
instance Pretty HsFieldUpdate where
	pretty (HsFieldUpdate name e) =
		myFsep [pretty name, equals, pretty e]

------------------------- Names -------------------------
instance Pretty HsQOp where
	pretty (HsQVarOp n) = ppHsQNameInfix n
	pretty (HsQConOp n) = ppHsQNameInfix n

ppHsQNameInfix :: HsQName -> Doc
ppHsQNameInfix name
	| isSymbolName (getName name) = ppHsQName name
	| otherwise = char '`' <> ppHsQName name <> char '`'

instance Pretty HsQName where
	pretty name = parensIf (isSymbolName (getName name)) (ppHsQName name)

ppHsQName :: HsQName -> Doc
ppHsQName (UnQual name) = ppHsName name
ppHsQName (Qual m name) = pretty m <> char '.' <> ppHsName name
ppHsQName (Special sym) = text (specialName sym)

instance Pretty HsOp where
	pretty (HsVarOp n) = ppHsNameInfix n
	pretty (HsConOp n) = ppHsNameInfix n

ppHsNameInfix :: HsName -> Doc
ppHsNameInfix name
	| isSymbolName name = ppHsName name
	| otherwise = char '`' <> ppHsName name <> char '`'

instance Pretty HsName where
	pretty name = parensIf (isSymbolName name) (ppHsName name)

ppHsName :: HsName -> Doc
ppHsName (HsIdent s)  = text s
ppHsName (HsSymbol s) = text s

instance Pretty HsCName where
	pretty (HsVarName n) = pretty n
	pretty (HsConName n) = pretty n

isSymbolName :: HsName -> Bool
isSymbolName (HsSymbol _) = True
isSymbolName _ = False

getName :: HsQName -> HsName
getName (UnQual s) = s
getName (Qual _ s) = s
getName (Special HsCons) = HsSymbol ":"
getName (Special HsFunCon) = HsSymbol "->"
getName (Special s) = HsIdent (specialName s)

specialName :: HsSpecialCon -> String
specialName HsUnitCon = "()"
specialName HsListCon = "[]"
specialName HsFunCon = "->"
specialName (HsTupleCon n) = "(" ++ replicate (n-1) ',' ++ ")"
specialName HsCons = ":"

ppHsContext :: HsContext -> Doc
ppHsContext []      = empty
ppHsContext context = mySep [parenList (map ppHsAsst context), text "=>"]

-- hacked for multi-parameter type classes

ppHsAsst :: HsAsst -> Doc
ppHsAsst (a,ts) = myFsep (ppHsQName a : map ppHsAType ts)

------------------------- pp utils -------------------------
maybePP :: (a -> Doc) -> Maybe a -> Doc
maybePP _ Nothing = empty
maybePP pp (Just a) = pp a

parenList :: [Doc] -> Doc
parenList = parens . myFsepSimple . punctuate comma

braceList :: [Doc] -> Doc
braceList = braces . myFsepSimple . punctuate comma

bracketList :: [Doc] -> Doc
bracketList = brackets . myFsepSimple

-- Wrap in braces and semicolons, with an extra space at the start in
-- case the first doc begins with "-", which would be scanned as {-
flatBlock :: [Doc] -> Doc
flatBlock = braces . (space <>) . hsep . punctuate semi

-- Same, but put each thing on a separate line
prettyBlock :: [Doc] -> Doc
prettyBlock = braces . (space <>) . vcat . punctuate semi

-- Monadic PP Combinators -- these examine the env

blankline :: Doc -> Doc
blankline dl = do{e<-getPPEnv;if spacing e && layout e /= PPNoLayout
			      then space $$ dl else dl}
topLevel :: Doc -> [Doc] -> Doc
topLevel header dl = do
	 e <- fmap layout getPPEnv
	 case e of
	     PPOffsideRule -> header $$ vcat dl
	     PPSemiColon -> header $$ prettyBlock dl
	     PPInLine -> header $$ prettyBlock dl
	     PPNoLayout -> header <+> flatBlock dl

ppBody :: (PPHsMode -> Int) -> [Doc] -> Doc
ppBody f dl = do
	e <- fmap layout getPPEnv
	i <- fmap f getPPEnv
	case e of
	    PPOffsideRule -> nest i . vcat $ dl
	    PPSemiColon   -> nest i . prettyBlock $ dl
	    _             -> flatBlock dl

ppBindings :: [Doc] -> Doc
ppBindings dl = do
	e <- fmap layout getPPEnv
	case e of
	    PPOffsideRule -> vcat dl
	    PPSemiColon   -> vcat . punctuate semi $ dl
	    _             -> hsep . punctuate semi $ dl

($$$) :: Doc -> Doc -> Doc
a $$$ b = layoutChoice (a $$) (a <+>) b

mySep :: [Doc] -> Doc
mySep = layoutChoice mySep' hsep
	where
	-- ensure paragraph fills with indentation.
	mySep' [x]    = x
	mySep' (x:xs) = x <+> fsep xs
	mySep' []     = error "Internal error: mySep"

myVcat :: [Doc] -> Doc
myVcat = layoutChoice vcat hsep

myFsepSimple :: [Doc] -> Doc
myFsepSimple = layoutChoice fsep hsep

-- same, except that continuation lines are indented,
-- which is necessary to avoid triggering the offside rule.
myFsep :: [Doc] -> Doc
myFsep = layoutChoice fsep' hsep
	where	fsep' [] = empty
		fsep' (d:ds) = do
			e <- getPPEnv
			let n = onsideIndent e
			nest n (fsep (nest (-n) d:ds))

layoutChoice :: (a -> Doc) -> (a -> Doc) -> a -> Doc
layoutChoice a b dl = do e <- getPPEnv
                         if layout e == PPOffsideRule ||
                            layout e == PPSemiColon
                          then a dl else b dl

-- Prefix something with a LINE pragma, if requested.
-- GHC's LINE pragma actually sets the current line number to n-1, so
-- that the following line is line n.  But if there's no newline before
-- the line we're talking about, we need to compensate by adding 1.

markLine :: SrcLoc -> Doc -> Doc
markLine loc doc = do
	e <- getPPEnv
	let y = srcLine loc
	let line l =
	      text ("{-# LINE " ++ show l ++ " \"" ++ srcFilename loc ++ "\" #-}")
	if linePragmas e then layoutChoice (line y $$) (line (y+1) <+>) doc
	      else doc

