{
{-| There are three shift\/reduce conflicts:

    > \x -> x + y

    can be parsed (incorrectly) as @(\\x -> x) + y@ or
    (correctly) as @\\x -> x + y@. The parser will @shift@ and hence do the
    right thing. The same problem occurs for @`op`@ and @->@ in place of @+@.
-}
module Syntax.Parser (
    -- * Exported Functions
    parse
    , parseFile
    , parseLiterate
    , parseLiterateFile
    , programParser
    , termParser
    , tokensParser
{-  REMOVE_IF_HADDOCK
    -- * Private Functions
    , mkLam
    , mkPi
    , mkInfix
    REMOVE_IF_HADDOCK -}
    ) where

import Syntax.Position
import Syntax.ParseMonad
import Syntax.Concrete
import Syntax.Lexer

import Utils.Monads

}

%name termParser Term
%name programParser Program
%name tokensParser Tokens
%tokentype { Token }
%monad { Parser }
%lexer { lexer } { TkEOF }
-- %expect 3

%token
    '('	    { TkLParen $$ }
    ')'	    { TkRParen $$ }
    '\\'    { TkLambda $$ }
    '->'    { TkArrow $$ }
    '_'     { TkUnderscore $$ }
    id	    { TkId $$ }
    int	    { TkInt $$ }
    atom    { TkAtom $$ }
    ':'	    { TkColon $$ }
    univ    { TkUniverse $$ }
    let	    { TkLet $$ }
    in	    { TkIn $$ }
    of	    { TkOf $$ }
    data    { TkData $$ }
    where   { TkWhere $$ }
    Star    { TkStar $$ }
    Set	    { TkSet $$ }
    ISet    { TkISet $$ }
    Prop    { TkProp $$ }
    Type    { TkType $$ }
    infix   { TkInfix $$ }
    infixl  { TkInfixL $$ }
    infixr  { TkInfixR $$ }
    plugin  { TkPlugin $$ }
    sig	    { TkSig $$ }
    struct  { TkStruct $$ }
    '{'	    { TkOpenBrace $$ }
    '}'	    { TkCloseBrace $$ }
    '['	    { TkOpenSquare $$ }
    ']'	    { TkCloseSquare $$ }
    vopen   { TkVOpenBrace $$ }
    vclose  { TkVCloseBrace $$ }
    '='	    { TkEqual $$ }
    ';'	    { TkSemi $$ }
    vsemi   { TkVSemi $$ }
    ','	    { TkComma $$ }
    '`'	    { TkBackQuote $$ }
    '.'	    { TkDot $$ }
    '?'	    { TkOp ($$,"?") }
    op	    { TkOp $$ }
    TeX	    { TkTeX $$ }

%%

-- Tokens

Token
    : '('	{ TkLParen $1 }
    | ')'	{ TkRParen $1 }
    | '\\'	{ TkLambda $1 }
    | '->'	{ TkArrow $1 }
    | '_'	{ TkUnderscore $1 }
    | id	{ TkId $1 }
    | atom	{ TkAtom $1 }
    | int	{ TkInt $1 }
    | ':'	{ TkColon $1 }
    | univ	{ TkUniverse $1 }
    | let	{ TkLet $1 }
    | in	{ TkIn $1 }
    | of	{ TkOf $1 }
    | data	{ TkData $1 }
    | where	{ TkWhere $1 }
    | Star	{ TkStar $1 }
    | Set	{ TkSet $1 }
    | ISet	{ TkISet $1 }
    | Prop	{ TkProp $1 }
    | Type	{ TkType $1 }
    | infix	{ TkInfix $1 }
    | infixl	{ TkInfixL $1 }
    | infixr	{ TkInfixR $1 }
    | plugin	{ TkPlugin $1 }
    | sig	{ TkSig $1 }
    | struct	{ TkStruct $1 }
    | '{'	{ TkOpenBrace $1 }
    | '}'	{ TkCloseBrace $1 }
    | '['	{ TkOpenSquare $1 }
    | ']'	{ TkCloseSquare $1 }
    | vopen	{ TkVOpenBrace $1 }
    | vclose	{ TkVCloseBrace $1 }
    | '='	{ TkEqual $1 }
    | ';'	{ TkSemi $1 }
    | vsemi	{ TkVSemi $1 }
    | ','	{ TkComma $1 }
    | '`'	{ TkBackQuote $1 }
    | '.'	{ TkDot $1 }
    | '?'	{ TkOp ($1,"?") }
    | op	{ TkOp $1 }
    | TeX	{ TkTeX $1 }

Tokens	: Token Tokens		{ $1 : $2 }
	|			{ [] }

-- Programs

Program : Init Tops		{ $2 }

-- Definitions

Top :	topen MaybeDefs close	{ $2 }

Tops
    : Top		{ $1 }
    | Top TeX Tops	{ $1 ++ $3 }
    | TeX Tops		{ $2 }

topen :				{% pushCurrentContext }

Definitions
    : '{' MaybeDefs '}'		{ $2 }
    | vopen MaybeDefs close	{ $2 }

close	: vclose	{ () }
	| error		{% popContext }

semi	: ';'		{ $1 }
	| vsemi		{ $1 }

-- Definitions must be separated by semicolons; however, we are quite liberal.
-- For instance, they can be separated by multiple semicolons, and trailing
-- semicolons after the last definition are also allowed.

-- Not anymore, we aren't. (Not necessary with layout?)

MaybeDefs
    :			    { [] }
    | Def		    { [$1] }
    | Def semi MaybeDefs    { $1:$3 }

Def : Var Patterns '=' Term Where
			{ mkFunClause	(fuseRange (fst $1) $4)
					(snd $1) $2 $4 $5
			}
    | Pattern1 InfixOp Pattern1 '=' Term Where
			{ mkFunClause	(fst $2)    -- the range says where the defined name is
					(snd $2) [$1,$3] $5 $6
			}
    | Axiom				    { $1 }
    | data Var Telescope ':' Term where
	Constructors			    { mkData $2 $3 $5 $7 }
    | infix int CommaOps		    { mkInfix NonAssoc $1 $2 $3 }
    | infixl int CommaOps		    { mkInfix LeftAssoc $1 $2 $3 }
    | infixr int CommaOps		    { mkInfix RightAssoc $1 $2 $3 }

Axiom
    : Var Telescope ':' Term	{ TypeSig
				    (fuseRange (fst $1) $4)
				    (snd $1) $2 $4
				}

Where
    :					    { [] }
    | where LocalDefs			    { $2 }

Constructors
    : '{' Constrs '}'			    { $2 }
    | vopen Constrs vclose		    { $2 }

Constrs
    : Var ':' Term semi Constrs    { Constructor (fuseRange (fst $1) $3)
						    (snd $1) $3 : $5 }
    | Var ':' Term		    { [Constructor (fuseRange (fst $1) $3)
						    (snd $1) $3
					] }
    |				    { [] }

Patterns
    : Patterns1	    { $1 }
    |		    { [] }

Patterns1
    : Pattern Patterns1	    { $1 : $2 }
    | Pattern		    { [$1] }

Pattern0
    : Pattern0 InfixOp Pattern1	{ InfixConP $1 $2 $3 }
    | Pattern1			{ $1 }

Pattern1
    : Var Patterns1		{ ConP (fuseRange (fst $1) (last $2))
					(snd $1) $2 }
    | Pattern			{ $1 }

Pattern
    : Var			    { uncurry VarP $1 }
    | int			    { uncurry mkNatP $1 }
    | '_'			    { WildP $1 }
    | '[' MaybePatList ']'	    { mkListP (fuseRange $1 $3) $2 }
    | '(' Pattern0 ')'		    { $2 }
    | '(' Pattern0 ',' PatList ')'  { mkPairP (fuseRange $1 $5) ($2:$4) }

-- We allow a restricted form of patterns [ x | (p,p) ] in Pis and Lambdas.
LamPattern
    : Var				{ uncurry VarP $1 }
    | '_'				{ WildP $1 }
    | '(' LamPattern ',' LamPatList ')'	{ mkPairP (fuseRange $1 $5) ($2:$4) }

LamPatList
    : LamPattern		{ [$1] }
    | LamPattern ',' LamPatList	{ $1 : $3 }

SpaceLamPats
    : LamPattern		{ [$1] }
    | LamPattern SpaceLamPats	{ $1 : $2 }

LocalDefs : Definitions	{ $1 }

-- Telescope
Telescope
    : Telescopes    { $1 }
    | 		    { [] }

Telescopes
    : '(' PatList ':' Term ')' Telescopes {% mkTelescope $2 $4 $6 }
    | '(' PatList ':' Term ')'            {% mkTelescope $2 $4 [] }

SigmaEntry
    : CommaTermNames ':' Term	    { ($1,$3) }
    | Term			    { (["_"],$1) }

SigmaTel0
    : SigmaEntry ';' SigmaTel0	{ $1 : $3 }
    | SigmaEntry		{ [$1] }

SigmaTel
    : SigmaEntry ';' SigmaTel0	{ $1 : $3 }

SigTel
    : SigEntry semi SigTel	{ $1 : $3 }
    | SigEntry			{ [$1] }

SigEntry
    : CommaNames ':' Term	{ ($1,$3) }

Struct
    : StructEntry semi Struct	{ $1 : $3 }
    | StructEntry		{ [$1] }

StructEntry
    : Name '=' Term		{ ($1,$3) }

--bang	: op				{% isBang $1 }

Projection
    : int	{% fstOrSnd $1 }
    | Var	{ uncurry Field $1 }

-- Terms

Term
	-- should really be a list of vars, but we have to
	-- parse it as a TermList to avoid conflicts with
	-- the pair syntax
    : '(' TermList ':' Term ')' '->' Term
				    {% mkPi (fuseRange $1 $7)
					    $2 $4 $7
				    }
    | Term1 '->' Term		    { Pi    (fuseRange $1 $3)
						(WildP (getRange $1)) $1 $3 }
    | Term1			    { $1 }

Term1
    : Term1 InfixOp Term2		{ InfixApp $1 $2 $3 }
    | Term2				{ $1 }

Term2
    : '\\' SpaceLamPats '->' Term   { mkLam (fuseRange $1 $4)
						    $2 $4
				    }
    | let LocalDefs in Term	    { Let   (fuseRange $1 $4)
					    $2 $4
				    }
    | Term3			    { $1 }

Term3
    : Term3 Term4		    { App $1 $2 }
    | Term3 '{' Term '}'	    { HApp $1 $3 }
    | Term3 of vopen Branches vclose
				    {% mkCase (fuseRange $1 $5) $1 $4 }
    | Term4			    { $1 }

Term4
    : Term4 '.' Projection		    { Project (fuseRange $1 $3)
							$1 $3 }
    | Term5				    { $1 }

-- Atomic Terms

Term5
    : Var				    { uncurry Name $1 }
    | int				    { uncurry mkNat $1 }
    | Universe				    { $1 }
    | plugin '(' MaybeTermList ')'          { CallPlugin (fuseRange (fst $1) $4)
						    (snd $1) $3
					    }
    | '?'				    { CallPlugin $1 "assert" [] }
    | '(' Term ')'			    { Paren (fuseRange $1 $3) $2 }
    | '[' MaybeTermList ']'		    { mkList (fuseRange $1 $3) $2 }
    | '{' SigmaTel '}'			    {% mkSigma (fuseRange $1 $3) $2 }
    | sig vopen SigTel vclose		    {% mkSig (fuseRange $1 $4) $3 }
    | sig '{' SigTel '}'		    {% mkSig (fuseRange $1 $4) $3 }
    | struct '{' Struct '}'		    {% mkStruct (fuseRange $1 $4) $3 }
    | struct vopen Struct vclose	    {% mkStruct (fuseRange $1 $4) $3 }
    | '(' Term ',' TermList ')'		    { mkPair (fuseRange $1 $5) ($2:$4) }

Branches
    : Branch		    { [$1] }
    | Branch semi Branches  { $1 : $3 }

Branch
    : Terms '->' Term	    { Branch $1 $3 }

Terms
    : Term4		    { [$1] }
    | Term4 Terms	    { $1 : $2 }

Universe
    : univ				    {% mkUniv $1 }
    | ISet				    { ISet $1 }
    | Star				    { uncurry Star $1 }
    | Set				    {% mkSet $1 }
    | Prop				    {% mkProp $1 }
    | Type				    {% mkType $1 }

InfixOp
    : '`' id '`'			    { $2 }
    | op				    { $1 }

MaybeTermList
    :                                       { [] }
    | TermList                              { $1 }

TermList
    : Term                                  { [$1] }
    | Term ',' TermList                     { $1 : $3 }

MaybePatList
    :                                   { [] }
    | PatList                           { $1 }

PatList
    : Pattern0				{ [$1] }
    | Pattern0 ',' PatList		{ $1 : $3 }

-- Names
-- "_" is a special identifier which may be the name of an abstraction
-- (in Lam and Pi), but it can never be referred to as variable.

--SpaceNames
--    : NameOrUnderscore		    { [$1] }
--    | NameOrUnderscore SpaceNames   { $1 : $2 }

CommaNames
    : Name		    { [$1] }
    | Name ',' CommaNames   { $1 : $3 }

CommaTermNames
    : Term			{% do x <- isName $1; return [x] }
    | Term ',' CommaTermNames   {% do x <- isName $1; return (x:$3) }

CommaOps
    : InfixOp		    { [$1] }
    | InfixOp ',' CommaOps  { $1 : $3 }

-- NameOrUnderscore 
--     : '_'                                   { "_" }     -- without Range
--     | Name                                  { $1 }

Name : Var				    { snd $1 }  -- without Range

Var : id				    { $1 }      -- with Range
    | atom				    { let (r,x) = $1 in (r,"\"" ++ x ++ "\"") }
    | '(' op ')'			    { $2 }

Init : { }

{

-- Parsing

parse :: Parser a -> Bool -> String -> ParseResult a
parse p poly = parse' flags 0 p
    where
	flags = defaultParseFlags { flagUniversePolymorphism = poly }

parseFile :: Parser a -> Bool -> FilePath -> IO (ParseResult a)
parseFile p poly = parseFile' flags 0 p
    where
	flags = defaultParseFlags { flagUniversePolymorphism = poly }

parseLiterate :: Parser a -> Bool -> String -> ParseResult a
parseLiterate p poly = parse' flags tex p
    where
	flags = defaultParseFlags { flagUniversePolymorphism = poly }

parseLiterateFile :: Parser a -> Bool -> FilePath -> IO (ParseResult a)
parseLiterateFile p poly = parseFile' flags tex p
    where
	flags = defaultParseFlags { flagUniversePolymorphism = poly }

programParser	:: Parser Program
termParser	:: Parser Term
tokensParser	:: Parser [Token]

happyError = fail "Parse error"

isBang (_,"!")	= return ()
isBang _	= fail "Expected '!'"

isName :: Term -> Parser Name
isName (Name _ x)   = return x
isName _	    = fail "Expected a name, found a term"

oneofId xs (r,y)
    | elem y xs	= return (r,y)
    | otherwise	= fail $ "Expected one of " ++ unwords xs

-- Sorts
mkUniv (r,n) =
    ifM withUniversePolymorphism
	(fail "#n cannot be used when universe polymorphism is enabled")
	(return $ Hash r (Univ n))
mkSet r = ifM withUniversePolymorphism
	    (return $ Set r)
	    (return $ Hash r $ Univ 0)

mkProp r = --ifM withUniversePolymorphism
	    (return $ Prop r)
	    --(return $ Name r "Prop")

mkType r = ifM withUniversePolymorphism
	    (return $ Type r)
	    (return $ Hash r $ Univ 1)

mkRule (r,"Pi") s t u	    = PiRule (fuseRange r u) s t u
mkRule (r,"Sigma") s t u    = SigmaRule (fuseRange r u) s t u

-- | Even though this function is not exported, I want it to show up
--   in the documentation.
mkLam :: Range -> [Pattern] -> Term -> Term
mkLam r vs t = foldr (Lam r) t vs

mkPi :: Range -> [Term] -> Term -> Term -> Parser Term
mkPi r vs t u
    | all isLamPat vs	= return $ foldr (\v -> Pi r v t) u $ map getLamPat vs
    | otherwise		= happyError
    where
	isLamPat (Name _ _)	= True
	isLamPat (Pair _ p q)	= isLamPat p && isLamPat q
	isLamPat _		= False

	getLamPat (Name r "_")	= WildP r
	getLamPat (Name r x)	= VarP r x
	getLamPat (Pair r p q)	= PairP r (getLamPat p) (getLamPat q)

mkSig :: Range -> [([Name], Term)] -> Parser Term
mkSig = mkSigmaOrSig FieldName

mkSigma :: Range -> [([Name], Term)] -> Parser Term
mkSigma = mkSigmaOrSig LocalName

mkSigmaOrSig :: IsField -> Range -> [([Name], Term)] -> Parser Term
mkSigmaOrSig f r tel = mkSigma' tel'
    where
	tel' = concatMap (\(xs,t) -> [ (x,t) | x <- xs ]) tel
	mkSigma' [_]		= fail "Sigma types must have at least two components"
	mkSigma' [(x,t),(y,u)]	= return $ Sigma (getRange t) f x t (field y) u
	mkSigma' ((x,t):tel)	= Sigma (getRange t) f x t "_" <$> mkSigma' tel

	field x = case f of
		    LocalName	-> "_"
		    FieldName	-> x

mkStruct :: Range -> [(Name, Term)] -> Parser Term
mkStruct r [_]		    = fail "Structs must have at least two components"
mkStruct r [(x,s),(y,t)]    = return $ Struct r x s y t
mkStruct r ((x,t):s)	    = Struct r x t "_" <$> mkStruct r s

mkPair :: Range -> [Term] -> Term
mkPair r ts = foldr1 (Pair r) ts

mkPairP :: Range -> [Pattern] -> Pattern
mkPairP r ps = foldr1 (PairP r) ps

mkInfix :: Assoc -> Range -> (Range, Precedence) -> [(Range, Name)] -> Decl
mkInfix ass r n vs =
    Infix   (fuseRange r (fst (last vs)))
	    ass (snd n) (map snd vs)

mkTelescope :: [Pattern] -> Term -> Telescope -> Parser Telescope
mkTelescope ps t tel =
    do	xs <- mapM isVar ps
	return $ map (\x -> (x,t)) xs ++ tel
    where
	isVar (VarP r x) = return $ V r x
	isVar p		 = fail "Patterns are not allowed in telescopes"

mkFunClause :: Range -> Name -> [Pattern] -> Term -> [Decl] -> Decl
mkFunClause r x ps e [] = FunClause r x ps e
mkFunClause r x ps e ds	= FunClause r x ps (Let r' ds e)
    where
	r' = fuseRange (head ds) (last ds)

-- | TODO: give correct range!
mkData (r,x) tel t []	= Data (fuseRange r t) x tel t []
mkData (r,x) tel t cs = Data (fuseRange r (last cs)) x tel t cs

-- | Hard coded names for zero and succ!
mkNat :: Range -> Int -> Term
mkNat r 0 = Name r "zero"
mkNat r n = App (Name r "succ") (mkNat r (n - 1))

mkNatP :: Range -> Int -> Pattern
mkNatP r 0 = VarP r "zero"
mkNatP r n = ConP r "succ" [mkNatP r (n - 1)]

mkList :: Range -> [Term] -> Term
mkList r []	= Name r "nil"
mkList r (x:xs) = Name r "::" `App` x `App` mkList r xs

mkListP :: Range -> [Pattern] -> Pattern
mkListP r []	    = VarP r "nil"
mkListP r (x:xs)    = ConP r "::" [x, mkListP r xs]

fstOrSnd :: (Range, Int) -> Parser Projection
fstOrSnd (r,1)	= return (Fst r)
fstOrSnd (r,2)	= return (Snd r)
fstOrSnd _	= fail "Only 1st or 2nd projections allowed."

mkCase :: Range -> Term -> [Branch] -> Parser Term
mkCase r t bs =
    case t of
	HApp t p    -> mkCase' t (Just p)
	_	    -> mkCase' t Nothing
    where
	mkCase' t mp =
	    case appView t of
		[_]	-> fail $ "Missing scrutinee in case expression."
		h:as	-> return $ Case r h as mp bs
	    where
		appView (App t1 t2) = appView t1 ++ [t2]
		appView t = [t]

}
