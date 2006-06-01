{-# OPTIONS -cpp -fglasgow-exts -fallow-overlapping-instances -fallow-undecidable-instances #-}

{-| The translation of abstract syntax to concrete syntax has two purposes.
    First it allows us to pretty print abstract syntax values without having to
    write a dedicated pretty printer, and second it serves as a sanity check
    for the concrete to abstract translation: translating from concrete to
    abstract and then back again should be (more or less) the identity.
-}
module Syntax.Translation.AbstractToConcrete where

import Control.Monad.Reader
import Data.Char

import Syntax.Common
import Syntax.Position
import Syntax.Info
import Syntax.Fixity
import Syntax.Concrete as C
import Syntax.Abstract as A

import Utils.Maybe
import Utils.Monad
import Utils.Tuple

#include "../../undefined.h"

-- Flags ------------------------------------------------------------------

-- | The translation is configurable. Currently you can choose whether to
--   make use of the pieces of concrete syntax stored in the info parts of
--   the abstract syntax. When pretty printing, this is what you want, but
--   if the purpose is to verify the correctness of the translation from
--   concrete to abstract we want to look at all of the abstract syntax.
data Flags = Flags  { useStoredConcreteSyntax :: Bool
		    , precedenceLevel	      :: Precedence
		    }

defaultFlags :: Flags
defaultFlags = Flags { useStoredConcreteSyntax	= True
		     , precedenceLevel		= TopCtx
		     }

-- The Monad --------------------------------------------------------------

-- | We make the translation monadic for modularity purposes.
type AbsToCon = Reader Flags

abstractToConcrete :: ToConcrete a c => Flags -> a -> c
abstractToConcrete flags a = runReader (toConcrete a) flags

abstractToConcreteCtx :: ToConcrete a c => Precedence -> a -> c
abstractToConcreteCtx ctx x =
    abstractToConcrete (defaultFlags { precedenceLevel = ctx }) x

abstractToConcrete_ :: ToConcrete a c => a -> c
abstractToConcrete_ = abstractToConcrete defaultFlags

-- Dealing with stored syntax ---------------------------------------------

-- | Indicates that the argument is a stored piece of syntax which
--   should only be used 
stored :: a -> AbsToCon (Maybe a)
stored x =
    do	b <- useStoredConcreteSyntax <$> ask
	return $ if b then Just x else Nothing

withStored :: ToConcrete i (Maybe c) => i -> AbsToCon c -> AbsToCon c
withStored i m = fromMaybeM m (toConcrete i)

-- Dealing with precedences -----------------------------------------------

-- | General bracketing function.
bracket' ::    (e -> e)		    -- ^ the bracketing function
	    -> (Precedence -> Bool) -- ^ do we need brackets
	    -> e -> AbsToCon e
bracket' paren needParen e =
    do	p <- precedenceLevel <$> ask
	return $ if needParen p then paren e else e

-- | Expression bracketing
bracket :: (Precedence -> Bool) -> AbsToCon C.Expr -> AbsToCon C.Expr
bracket par m =
    do	e <- m
	bracket' (Paren (getRange e)) par e

-- | Pattern bracketing
bracketP :: (Precedence -> Bool) -> AbsToCon C.Pattern -> AbsToCon C.Pattern
bracketP par m =
    do	e <- m
	bracket' (ParenP (getRange e)) par e

-- Dealing with infix declarations ----------------------------------------

-- | If a name is defined with a fixity that differs from the default, we have
--   to generate a fixity declaration for that name.
withInfixDecl :: DefInfo -> C.Name -> AbsToCon [C.Declaration] -> AbsToCon [C.Declaration]
withInfixDecl i x m
    | defFixity i == defaultFixity  = m
    | otherwise			    =
	do  ds <- m
	    return $ C.Infix (defFixity i) [x] : ds

withInfixDecls :: [(DefInfo, C.Name)] -> AbsToCon [C.Declaration] -> AbsToCon [C.Declaration]
withInfixDecls = foldr (.) id . map (uncurry withInfixDecl)

-- Dealing with private definitions ---------------------------------------

withAbstractPrivate :: DefInfo -> AbsToCon [C.Declaration] -> AbsToCon [C.Declaration]
withAbstractPrivate i m =
    case (defAccess i, defAbstract i) of
	(PublicAccess, ConcreteDef) -> m
	(p,a)			    -> 
	    do	ds <- m
		return $ abst a $ priv p $ ds
    where
	priv PrivateAccess ds = [ C.Private (getRange ds) ds ]
	priv _ ds	      = ds
	abst AbstractDef ds   = [ C.Abstract (getRange ds) ds ]
	abst _ ds	      = ds

-- The To Concrete Class --------------------------------------------------

class ToConcrete a c | a -> c where
    toConcrete :: a -> AbsToCon c

-- | Translate something in a context of the given precedence.
toConcreteCtx :: ToConcrete a c => Precedence -> a -> AbsToCon c
toConcreteCtx p x = local (\f -> f { precedenceLevel = p }) $ toConcrete x

-- Info instances ---------------------------------------------------------

instance ToConcrete ExprInfo (Maybe C.Expr) where
    toConcrete (ExprSource _ f)	=
	do  p <- precedenceLevel <$> ask
	    stored (f p)
    toConcrete _		= return Nothing

instance ToConcrete DeclInfo (Maybe [C.Declaration]) where
    toConcrete = toConcrete . declSource

instance ToConcrete DeclSource (Maybe [C.Declaration]) where
    toConcrete (DeclSource ds)	= stored ds
    toConcrete _		= return Nothing

instance ToConcrete DefInfo (Maybe [C.Declaration]) where
    toConcrete info = toConcrete $ defInfo info

instance ToConcrete LHSInfo (Maybe C.LHS) where
    toConcrete (LHSSource lhs) = stored lhs

instance ToConcrete PatInfo (Maybe C.Pattern) where
    toConcrete (PatSource _ f) =
	do  p <- precedenceLevel <$> ask
	    stored (f p)
    toConcrete (PatRange _) = return Nothing

instance ToConcrete ModuleInfo (Maybe [C.Declaration]) where
    toConcrete = toConcrete . minfoSource

instance ToConcrete LetInfo (Maybe [C.Declaration]) where
    toConcrete (LetSource ds) = stored ds
    toConcrete _	      = return Nothing


-- General instances ------------------------------------------------------

instance ToConcrete a c => ToConcrete [a] [c] where
    toConcrete = mapM toConcrete

instance (ToConcrete a1 c1, ToConcrete a2 c2) => ToConcrete (a1,a2) (c1,c2) where
    toConcrete (x,y) = liftM2 (,) (toConcrete x) (toConcrete y)

instance (ToConcrete a1 c1, ToConcrete a2 c2, ToConcrete a3 c3) =>
	 ToConcrete (a1,a2,a3) (c1,c2,c3) where
    toConcrete (x,y,z) = reorder <$> toConcrete (x,(y,z))
	where
	    reorder (x,(y,z)) = (x,y,z)

newtype DontTouchMe a = DontTouchMe a

instance ToConcrete (DontTouchMe a) a where
    toConcrete (DontTouchMe x) = return x

-- | @Force@ is the type level equivalent of @fromJust@.
--   If @toConcrete a :: Maybe c@, then @toConcrete (Force a) :: c@
newtype Force a = Force a

instance ToConcrete a (Maybe c) => ToConcrete (Force a) c where
    toConcrete (Force a) =
	do  Just c <- local (\s -> s { useStoredConcreteSyntax = True })
			$ toConcrete a
	    return c

-- Names ------------------------------------------------------------------

instance ToConcrete A.Name C.Name where
    toConcrete = return . nameConcrete

instance ToConcrete A.QName C.QName where
    toConcrete = return . qnameConcrete

instance ToConcrete A.ModuleName C.QName where
    toConcrete = return . mnameConcrete

-- Expression instance ----------------------------------------------------

instance ToConcrete A.Expr C.Expr where
    toConcrete (Var i _) = return $ Ident (concreteName i)
    toConcrete (Def i _) = return $ Ident (concreteName i)
    toConcrete (Con i _) = return $ Ident (concreteName i)
	-- for names we have to use the name from the info, since the abstract
	-- name has been resolved to a fully qualified name (except for
	-- variables)
    toConcrete (A.Lit l)	    = return $ C.Lit l
    toConcrete (A.QuestionMark i)   = return $ C.QuestionMark
						(getRange i)
						(metaNumber i)
    toConcrete (A.Underscore i)	    = return $ C.Underscore
						(getRange i)
						(metaNumber i)

    toConcrete (A.App i (A.App _ eop (Arg NotHidden e1)) (Arg NotHidden e2))
	| Just (fx,op) <- isOp eop =
	    bracket (infixBrackets fx)
	    $ do e1 <- toConcreteCtx (LeftOperandCtx fx) e1
		 e2 <- toConcreteCtx (RightOperandCtx fx) e2
		 return $ C.InfixApp e1 op e2
	where
	    isOp (A.Var i x)
		| opStr (show x) = Just (nameFixity i, concreteName i)
	    isOp (A.Con i x)
		| opStr (show x) = Just (nameFixity i, concreteName i)
	    isOp (A.Def i x)
		| opStr (show x) = Just (nameFixity i, concreteName i)
	    isOp _ = Nothing

	    opStr (c:_) = not (isAlpha c || c == '_')
	    opStr _	= __IMPOSSIBLE__

    toConcrete (A.App i e1 e2)    =
	withStored i
	$ bracket appBrackets
	$ do e1' <- toConcreteCtx FunctionCtx e1
	     e2' <- toConcreteCtx ArgumentCtx e2
	     return $ C.App (getRange i) e1' e2'

    toConcrete e@(A.Lam i _ _)	    =
	withStored i
	$ bracket lamBrackets
	$ case lamView e of
	    (bs, e) ->
		do  bs <- toConcrete bs
		    e  <- toConcreteCtx TopCtx e
		    return $ C.Lam (getRange i) bs e
	where
	    lamView (A.Lam _ b@(A.DomainFree _ _) e) =
		case lamView e of
		    ([], e)			   -> ([b], e)
		    (bs@(A.DomainFree _ _ : _), e) -> (b:bs, e)
		    _				   -> ([b], e)
	    lamView (A.Lam _ b@(A.DomainFull _) e) =
		case lamView e of
		    ([], e)			   -> ([b], e)
		    (bs@(A.DomainFull _ : _), e)   -> (b:bs, e)
		    _				   -> ([b], e)
	    lamView e = ([], e)

    toConcrete (A.Pi i b e)	    =
	withStored i
	$ bracket piBrackets
	$ do b' <- toConcrete b
	     e' <- toConcreteCtx TopCtx e
	     return $ C.Pi b' e'

    toConcrete (A.Fun i a b) =
	withStored i
	$ bracket piBrackets
	$ do a' <- toConcreteCtx FunctionSpaceDomainCtx a 
	     b' <- toConcreteCtx TopCtx b
	     return $ C.Fun (getRange i) a' b'

    toConcrete (A.Set i 0)  = withStored i $ return $ C.Set (getRange i)
    toConcrete (A.Set i n)  = withStored i $ return $ C.SetN (getRange i) n
    toConcrete (A.Prop i)   = withStored i $ return $ C.Prop (getRange i)

    toConcrete (A.Let i ds e) =
	withStored i
	$ bracket lamBrackets
	$ do ds' <- concat <$> toConcrete ds
	     e'  <- toConcreteCtx TopCtx e
	     return $ C.Let (getRange i) ds' e'

-- Binder instances -------------------------------------------------------

instance ToConcrete A.LamBinding C.LamBinding where
    toConcrete (A.DomainFree h x) = C.DomainFree h <$> toConcrete x
    toConcrete (A.DomainFull b)   = C.DomainFull <$> toConcrete b

instance ToConcrete A.TypedBinding C.TypedBinding where
    toConcrete (A.TypedBinding r h xs e) =
	C.TypedBinding r h <$> toConcrete xs <*> toConcreteCtx TopCtx e

-- Declaration instances --------------------------------------------------

instance ToConcrete [A.Declaration] [C.Declaration] where
    toConcrete ds = concat <$> mapM toConcrete ds

instance ToConcrete LetBinding [C.Declaration] where
    toConcrete (LetBind i x t e) =
	withStored i $
	do  (x,t,e) <- toConcrete (x,t,e)
	    return [C.TypeSig x t, C.FunClause (C.LHS (getRange x) PrefixDef x []) e []]

data TypeAndDef = TypeAndDef A.TypeSignature A.Definition

instance ToConcrete TypeAndDef [C.Declaration] where

    -- We don't do withInfixDecl here. It's done at the declaration level.

    toConcrete (TypeAndDef (Axiom _ x t) (FunDef i _ cs)) =
	withAbstractPrivate i $
	do  t'  <- toConcreteCtx TopCtx t
	    cs' <- withStored i $ toConcrete cs
	    x'  <- toConcrete x
	    return $ TypeSig x' t' : cs'

    toConcrete (TypeAndDef (Axiom _ x t) (DataDef i _ bs cs)) =
	withAbstractPrivate i $
	withStored  i $
	do  tel'     <- toConcrete tel
	    t'	     <- toConcreteCtx TopCtx t0
	    (x',cs') <- toConcrete (x, map Constr cs)
	    return [ C.Data (getRange i) x' tel' t' cs' ]
	where
	    (tel, t0) = mkTel (length bs) t
	    mkTel 0 t		    = ([], t)
	    mkTel n (A.Pi _ b t)    = (b:) -*- id $ mkTel (n - 1) t
	    mkTel _ _		    = __IMPOSSIBLE__

    toConcrete _ = __IMPOSSIBLE__

newtype Constr a = Constr a

instance ToConcrete (Constr A.Constructor) C.Declaration where
    toConcrete (Constr (A.Axiom i x t)) =
	C.TypeSig <$> toConcrete x <*> toConcreteCtx TopCtx t
    toConcrete _ = __IMPOSSIBLE__

instance ToConcrete A.Clause C.Declaration where
    toConcrete (A.Clause lhs rhs wh) =
	do  lhs' <- toConcrete lhs
	    rhs' <- toConcreteCtx TopCtx rhs
	    wh'  <- toConcrete wh
	    return $ FunClause lhs' rhs' wh'

instance ToConcrete A.Declaration [C.Declaration] where

    toConcrete (Axiom i x t) =
	do  x' <- toConcrete x
	    withAbstractPrivate	i  $
		withInfixDecl i x' $
		withStored    i    $
		do  t' <- toConcreteCtx TopCtx t
		    return [C.Postulate (getRange i) [C.TypeSig x' t']]

    toConcrete (Definition i ts ds) =
	do  ixs' <- toConcrete $ map (DontTouchMe -*- id) ixs
	    withInfixDecls ixs' $
		do  ds' <- concat <$> toConcrete (zipWith TypeAndDef ts ds)
		    return [C.Mutual (getRange i) ds']
	where
	    ixs = map getInfoAndName ts
	    is  = map fst ixs
	    getInfoAndName (A.Axiom i x _)  = (i,x)
	    getInfoAndName _		    = __IMPOSSIBLE__

    toConcrete (A.Module i x tel ds) =
	withStored i $
	do  (x',tel',ds')  <- toConcrete (x,tel,ds)
	    return [C.Module (getRange i) x' tel' ds']

    -- There is no way we could restore module defs, imports and opens
    -- without having the concrete version stored away.
    toConcrete (A.ModuleDef (ModuleInfo _ (DeclSource ds)) _ _ _ _)
					= return ds
    toConcrete (A.ModuleDef _ _ _ _ _)	= __IMPOSSIBLE__

    toConcrete (A.Import (ModuleInfo _ (DeclSource ds)) _) = return ds
    toConcrete (A.Import _ _) = __IMPOSSIBLE__

    toConcrete (A.Open (DeclSource ds))	= return ds
    toConcrete (A.Open _) = __IMPOSSIBLE__

-- Left hand sides --------------------------------------------------------

instance ToConcrete a c => ToConcrete (Arg a) (Arg c) where
    toConcrete (Arg h x) =
	Arg h <$> toConcreteCtx (hiddenArgumentCtx h) x

instance ToConcrete A.LHS C.LHS where
    toConcrete (A.LHS i x args) =
	withStored i $
	do  (x',args') <- toConcrete (x,args)
	    return $ C.LHS (getRange i) PrefixDef x' args'

instance ToConcrete A.Pattern C.Pattern where
    toConcrete (VarP x)		= IdentP . C.QName <$> toConcrete x
    toConcrete (A.WildP i)	=
	withStored i $ return $ C.WildP (getRange i)
    toConcrete (ConP i x args)  = toConcrete (Force i)
    toConcrete (A.AsP i x p)	= C.AsP (getRange i) <$> toConcrete x <*> toConcrete p
    toConcrete (A.AbsurdP i)	= return $ C.AbsurdP (getRange i)

--  We can't figure out the original name without looking at the stored
--  pattern.
-- 	withStored i $
-- 	do  args' <- toConcrete args
-- 	    return $ foldl appP (IdentP x) args'
-- 	where
-- 	    appP p (Arg h q) = AppP h p q
	

