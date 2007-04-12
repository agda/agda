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
import Data.Map as Map hiding (map)
import Data.List as List

import Syntax.Common
import Syntax.Position
import Syntax.Info
import Syntax.Fixity
import Syntax.Concrete as C
import Syntax.Concrete.Pretty
import Syntax.Abstract as A
import Syntax.Abstract.Views as AV
import Syntax.Scope.Base

import Utils.Maybe
import Utils.Monad
import Utils.Tuple

#include "../../undefined.h"

-- Environment ------------------------------------------------------------

-- | The translation is configurable. Currently you can choose whether to
--   make use of the pieces of concrete syntax stored in the info parts of
--   the abstract syntax. When pretty printing, this is what you want, but
--   if the purpose is to verify the correctness of the translation from
--   concrete to abstract we want to look at all of the abstract syntax.
data Env = Env { useStoredConcreteSyntax :: Bool
	       , precedenceLevel	 :: Precedence
	       , currentScope		 :: ScopeStack
	       }

defaultEnv :: Env
defaultEnv = Env { useStoredConcreteSyntax = True
		 , precedenceLevel	   = TopCtx
		 , currentScope		   = []
		 }

-- The Monad --------------------------------------------------------------

-- | We make the translation monadic for modularity purposes.
type AbsToCon = Reader Env

abstractToConcrete :: ToConcrete a c => Env -> a -> c
abstractToConcrete flags a = runReader (toConcrete a) flags

abstractToConcreteCtx :: ToConcrete a c => Precedence -> a -> c
abstractToConcreteCtx ctx x =
    abstractToConcrete (defaultEnv { precedenceLevel = ctx }) x

abstractToConcrete_ :: ToConcrete a c => a -> c
abstractToConcrete_ = abstractToConcrete defaultEnv

-- Dealing with names -----------------------------------------------------

lookupName :: A.Name -> AbsToCon C.Name
lookupName x =
    do	scope <- undefined  -- TODO!!
	case Map.lookup x scope of
	    Just y  -> return y
	    Nothing -> return $ nameConcrete x -- TODO: should be __IMPOSSIBLE__
					       -- (once we take the context
					       -- into account when translating)

bindName :: A.Name -> (C.Name -> AbsToCon a) -> AbsToCon a
bindName x ret = do
    names <- asks undefined -- TODO!!
    let y = nameConcrete x
    case Map.lookup y names of
	Just _	-> bindName (nextName x) ret
	Nothing	-> undefined -- TODO!!
-- 	    local (\e -> e { concreteNames = Map.insert x y $ concreteNames e
-- 			   , abstractNames = dontInsertNoName y x $ abstractNames e
-- 			   }
-- 		  ) $ ret y
    where
	dontInsertNoName y x m
	    | y == C.noName_ = m
	    | otherwise	     = Map.insert y x m

-- | TODO: Move
data Suffix = NoSuffix | Prime Int | Index Int

nextSuffix NoSuffix  = Prime 1
nextSuffix (Prime _) = Index 0	-- we only use single primes in generated names
nextSuffix (Index i) = Index $ i + 1

suffixView :: String -> (String, Suffix)
suffixView s
    | (ps@(_:_), s') <- span (=='\'') rs = (reverse s', Prime $ length ps)
    | (ns@(_:_), s') <- span isDigit rs	 = (reverse s', Index $ read $ reverse ns)
    | otherwise				 = (s, NoSuffix)
    where
	rs = reverse s

addSuffix :: String -> Suffix -> String
addSuffix s NoSuffix = s
addSuffix s (Prime n) = s ++ replicate n '\''
addSuffix s (Index i) = s ++ show i

nextName :: A.Name -> A.Name
nextName x = x { nameConcrete = C.Name r $ nextSuf ps }
    where
	C.Name r ps = nameConcrete x
	-- NoName cannot appear here
	nextSuf [Id s]	     = [ Id $ nextStr s ]
	nextSuf [Id s, Hole] = [ Id $ nextStr s, Hole ]
	nextSuf (p : ps)     = p : nextSuf ps
	nextSuf []	     = __IMPOSSIBLE__	-- noName cannot appear here
	nextStr s = case suffixView s of
	    (s0, suf) -> addSuffix s0 (nextSuffix suf)

-- Dealing with stored syntax ---------------------------------------------

-- | Indicates that the argument is a stored piece of syntax.
stored :: a -> AbsToCon (Maybe a)
stored x =
    do	b <- useStoredConcreteSyntax <$> ask
	return $ if b then Just x else Nothing

withStored :: ToConcrete i (Maybe c) => i -> AbsToCon c -> AbsToCon c
withStored i m = fromMaybeM m (toConcrete i)

bindWithStored :: BindToConcrete i (Maybe c) => i -> (c -> AbsToCon b) -> AbsToCon b -> AbsToCon b
bindWithStored i ret m = bindToConcrete i $ maybe m ret


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
bracketP :: (Precedence -> Bool) -> ([C.Pattern] -> AbsToCon a)
				 -> (([C.Pattern] -> AbsToCon a) -> AbsToCon a)
				 -> AbsToCon a
bracketP par ret m = m $ \ps -> do
    ps' <- mapM (bracket' (ParenP (getRange ps)) par) ps
    ret ps'

-- Dealing with infix declarations ----------------------------------------

-- | If a name is defined with a fixity that differs from the default, we have
--   to generate a fixity declaration for that name.
withInfixDecl :: DefInfo -> C.Name -> AbsToCon [C.Declaration] -> AbsToCon [C.Declaration]
withInfixDecl i x m
    | defFixity i == defaultFixity = m
    | otherwise			   = do
	ds <- m
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

class BindToConcrete a c | a -> c where
    bindToConcrete :: a -> (c -> AbsToCon b) -> AbsToCon b

-- | Translate something in a context of the given precedence.
toConcreteCtx :: ToConcrete a c => Precedence -> a -> AbsToCon c
toConcreteCtx p x = local (\f -> f { precedenceLevel = p }) $ toConcrete x

-- | Translate something in a context of the given precedence.
bindToConcreteCtx :: BindToConcrete a c => Precedence -> a -> (c -> AbsToCon b) -> AbsToCon b
bindToConcreteCtx p x ret = local (\f -> f { precedenceLevel = p }) $ bindToConcrete x ret

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

instance BindToConcrete LHSInfo (Maybe C.LHS) where
    bindToConcrete (LHSSource lhs) ret = ret =<< stored lhs

instance BindToConcrete PatInfo (Maybe [C.Pattern]) where
    bindToConcrete (PatSource _ f) ret =
	do  p <- precedenceLevel <$> ask
	    ret . fmap (:[]) =<< stored (f p)
    bindToConcrete (PatRange _) ret = ret Nothing

instance ToConcrete ModuleInfo (Maybe [C.Declaration]) where
    toConcrete = toConcrete . minfoSource

instance BindToConcrete LetInfo (Maybe [C.Declaration]) where
    bindToConcrete (LetSource ds) ret = ret =<< stored ds
    bindToConcrete _		  ret = ret Nothing


-- General instances ------------------------------------------------------

instance ToConcrete a c => ToConcrete [a] [c] where
    toConcrete = mapM toConcrete

instance BindToConcrete a c => BindToConcrete [a] [c] where
    bindToConcrete = thread bindToConcrete

instance (ToConcrete a1 c1, ToConcrete a2 c2) => ToConcrete (a1,a2) (c1,c2) where
    toConcrete (x,y) = liftM2 (,) (toConcrete x) (toConcrete y)

instance (BindToConcrete a1 c1, BindToConcrete a2 c2) => BindToConcrete (a1,a2) (c1,c2) where
    bindToConcrete (x,y) ret =
	bindToConcrete x $ \x ->
	bindToConcrete y $ \y ->
	ret (x,y)

instance (ToConcrete a1 c1, ToConcrete a2 c2, ToConcrete a3 c3) =>
	 ToConcrete (a1,a2,a3) (c1,c2,c3) where
    toConcrete (x,y,z) = reorder <$> toConcrete (x,(y,z))
	where
	    reorder (x,(y,z)) = (x,y,z)

instance (BindToConcrete a1 c1, BindToConcrete a2 c2, BindToConcrete a3 c3) =>
	 BindToConcrete (a1,a2,a3) (c1,c2,c3) where
    bindToConcrete (x,y,z) ret = bindToConcrete (x,(y,z)) $ ret . reorder
	where
	    reorder (x,(y,z)) = (x,y,z)

instance ToConcrete a c => ToConcrete (Arg a) (Arg c) where
    toConcrete (Arg h@Hidden    x) = Arg h <$> toConcreteCtx TopCtx x
    toConcrete (Arg h@NotHidden x) = Arg h <$> toConcrete x

instance ToConcrete a c => ToConcrete (Named name a) (Named name c) where
    toConcrete (Named n x) = Named n <$> toConcrete x

instance BindToConcrete a c => BindToConcrete (Arg a) (Arg c) where
    bindToConcrete (Arg h x) ret = bindToConcreteCtx (hiddenArgumentCtx h) x $ ret . Arg h

instance BindToConcrete a c => BindToConcrete (Named name a) (Named name c) where
    bindToConcrete (Named n x) ret = bindToConcrete x $ ret . Named n

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
    toConcrete = lookupName

instance ToConcrete A.QName C.QName where
    toConcrete = return . qnameToConcrete   -- TODO!!

instance BindToConcrete A.Name C.Name where
    bindToConcrete x = bindName x

-- Expression instance ----------------------------------------------------

instance ToConcrete A.Expr C.Expr where
    toConcrete (Var _ x) = Ident . C.QName <$> toConcrete x
    toConcrete (Def _ x) = return $ Ident (qnameToConcrete x) -- TODO!!
    toConcrete (Con _ x) = return $ Ident (qnameToConcrete x) -- TODO!!
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

    toConcrete e@(A.App i e1 e2)    =
	withStored i
        $ tryToRecoverOpApp e
        -- or fallback to App
	$ bracket appBrackets
        $ do e1' <- toConcreteCtx FunctionCtx e1
	     e2' <- toConcreteCtx ArgumentCtx e2
	     return $ C.App (getRange i) e1' e2'

    toConcrete e@(A.Lam i _ _)	    =
	withStored i
	$ bracket lamBrackets
	$ case lamView e of
	    (bs, e) ->
		bindToConcrete bs $ \bs -> do
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

    toConcrete (A.Pi _ [] e) = toConcrete e
    toConcrete (A.Pi i b e)  =
	withStored i
	$ bracket piBrackets
	$ bindToConcrete b $ \b' -> do
	     e' <- toConcreteCtx TopCtx e
	     return $ C.Pi b' e'

    toConcrete (A.Fun i a b) =
	withStored i
	$ bracket piBrackets
	$ do a' <- toConcreteCtx FunctionSpaceDomainCtx a 
	     b' <- toConcreteCtx TopCtx b
	     return $ C.Fun (getRange i) (mkArg a') b'
	where
	    mkArg (Arg Hidden	 e) = HiddenArg (getRange e) (unnamed e)
	    mkArg (Arg NotHidden e) = e

    toConcrete (A.Set i 0)  = withStored i $ return $ C.Set (getRange i)
    toConcrete (A.Set i n)  = withStored i $ return $ C.SetN (getRange i) n
    toConcrete (A.Prop i)   = withStored i $ return $ C.Prop (getRange i)

    toConcrete (A.Let i ds e) =
	withStored i
	$ bracket lamBrackets
	$ bindToConcrete ds $ \ds' -> do
	     e'  <- toConcreteCtx TopCtx e
	     return $ C.Let (getRange i) (concat ds') e'

    toConcrete (A.ScopedExpr scope e) = undefined -- TODO!!

-- Dot patterns can bind variables. This is how.
-- They can't anymore. Good, then we don't have to implement the instance.
{-
instance BindToConcrete A.Expr C.Expr where
    bindToConcrete e ret = __IMPOSSIBLE__ -- TODO: not really
-}

-- Binder instances -------------------------------------------------------

instance BindToConcrete A.LamBinding C.LamBinding where
    bindToConcrete (A.DomainFree h x) ret = bindToConcrete x $ ret . C.DomainFree h
    bindToConcrete (A.DomainFull b)   ret = bindToConcrete b $ ret . C.DomainFull

instance BindToConcrete A.TypedBindings C.TypedBindings where
    bindToConcrete (A.TypedBindings r h bs) ret =
	bindToConcrete bs $ \bs ->
	ret (C.TypedBindings r h bs)

instance BindToConcrete A.TypedBinding C.TypedBinding where
    bindToConcrete (A.TBind r xs e) ret =
	bindToConcrete xs $ \xs -> do
	e <- toConcreteCtx TopCtx e
	ret (C.TBind r xs e)
    bindToConcrete (A.TNoBind e) ret = do
	e <- toConcreteCtx TopCtx e
	ret (C.TNoBind e)

instance BindToConcrete LetBinding [C.Declaration] where
    bindToConcrete (LetBind i x t e) ret =
	bindWithStored i ret $
	bindToConcrete x $ \x ->
	do  (t,e) <- toConcrete (t,A.RHS e)
	    ret [C.TypeSig x t, C.FunClause (C.IdentP $ C.QName x) e []]

instance ToConcrete LetBinding [C.Declaration] where
    toConcrete b = bindToConcrete b return

-- Declaration instances --------------------------------------------------

instance ToConcrete [A.Declaration] [C.Declaration] where
    toConcrete ds = concat <$> mapM toConcrete ds

instance ToConcrete A.RHS C.RHS where
    toConcrete (A.RHS e)   = C.RHS <$> toConcrete e
    toConcrete A.AbsurdRHS = return C.AbsurdRHS

data TypeAndDef = TypeAndDef A.TypeSignature A.Definition

instance ToConcrete TypeAndDef [C.Declaration] where
  toConcrete _ = undefined
{-
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
	bindToConcrete tel $ \tel' -> do
	    t'	     <- toConcreteCtx TopCtx t0
	    (x',cs') <- toConcrete (x, map Constr cs)
	    return [ C.Data (getRange i) x' tel' t' cs' ]
	where
	    (tel, t0) = mkTel (length bs) t
	    mkTel 0 t		    = ([], t)
	    mkTel n (A.Pi _ b t)    = (b++) -*- id $ mkTel (n - 1) t
	    mkTel _ _		    = __IMPOSSIBLE__

    toConcrete _ = __IMPOSSIBLE__
-}

newtype Constr a = Constr a

instance ToConcrete (Constr A.Constructor) C.Declaration where
  toConcrete _ = undefined -- TODO!!
{-
    toConcrete (Constr (A.Axiom i x t)) = do
	x' <- toConcrete x
	t' <- toConcreteCtx TopCtx t
	return $ C.TypeSig x' t'
    toConcrete _ = __IMPOSSIBLE__
-}

instance ToConcrete A.Clause C.Declaration where
  toConcrete _ = undefined
{-
    toConcrete (A.Clause lhs rhs wh) =
	bindToConcrete lhs $ \lhs' -> do
	    rhs' <- toConcreteCtx TopCtx rhs
	    wh'  <- toConcrete wh
	    return $ FunClause lhs' rhs' wh'
-}

instance ToConcrete A.Declaration [C.Declaration] where

  toConcrete _ = undefined -- TODO!!

{-
    toConcrete (ScopedDecl _ _) = undefined -- TODO!!

    toConcrete (Axiom i x t) =
	do  x' <- toConcrete x
	    withAbstractPrivate	i  $
		withInfixDecl i x' $
		withStored    i    $
		do  t' <- toConcreteCtx TopCtx t
		    return [C.Postulate (getRange i) [C.TypeSig x' t']]

    toConcrete (A.Primitive i x t) =
	do  x' <- toConcrete x
	    withAbstractPrivate	i  $
		withInfixDecl i x' $
		withStored    i    $
		do  t' <- toConcreteCtx TopCtx t
		    return [C.Primitive (getRange i) [C.TypeSig x' t']]

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

    toConcrete (A.Section i x tel ds) = undefined -- TODO!!
    toConcrete (A.Apply i x y es) = undefined -- TODO!!

--     toConcrete (A.Module i x tel ds) =
-- 	withStored i $
-- 	do  x <- toConcrete x
-- 	    bindToConcrete tel $ \tel -> do
-- 		ds <- toConcrete ds
-- 		return [C.Module (getRange i) x tel ds]
-- 
--     -- There is no way we could restore module defs, imports and opens
--     -- without having the concrete version stored away.
--     toConcrete (A.ModuleDef (ModuleInfo _ _ (DeclSource ds)) _ _ _ _)
-- 					= return ds
--     toConcrete (A.ModuleDef _ _ _ _ _)	= __IMPOSSIBLE__

    toConcrete (A.Import (ModuleInfo _ _ (DeclSource ds)) _) = return ds
    toConcrete (A.Import _ _) = __IMPOSSIBLE__

    toConcrete (A.Pragma i p)	= do
	p <- toConcrete $ RangeAndPragma (getRange i) p
	return [C.Pragma p]
-}

data RangeAndPragma = RangeAndPragma Range A.Pragma

instance ToConcrete RangeAndPragma C.Pragma where
    toConcrete (RangeAndPragma r p) = case p of
	A.OptionsPragma xs  -> return $ C.OptionsPragma r xs
	A.BuiltinPragma b x -> do
	    x <- toConcrete x
	    return $ C.BuiltinPragma r b x

-- Left hand sides --------------------------------------------------------

concatArgs :: [NamedArg [C.Pattern]] -> [NamedArg C.Pattern]
concatArgs args = [ Arg h (Named name p) | Arg h (Named name [p]) <- args ]

instance BindToConcrete A.LHS C.Pattern where
    bindToConcrete (A.LHS i x args) ret =
	-- bindWithStored i ret $
	do  x <- toConcrete x
	    -- TODO: mixfix applications
	    bindToConcreteCtx ArgumentCtx args $ \args ->
		ret $ foldl C.AppP (IdentP x) $ concatArgs args

instance ToConcrete A.Pattern [C.Pattern] where
    toConcrete p = bindToConcrete p return

appBrackets' :: [arg] -> Precedence -> Bool
appBrackets' []	   _   = False
appBrackets' (_:_) ctx = appBrackets ctx

-- TODO: bracket patterns
instance BindToConcrete A.Pattern [C.Pattern] where
    bindToConcrete (VarP x)	   ret = bindToConcrete x $ ret . (:[]) . IdentP . C.QName
    bindToConcrete (A.WildP i)	   ret =
	ret [ C.WildP (getRange i) ]
    bindToConcrete (ConP i x args) ret =
	bracketP (appBrackets' args) ret $ \ret -> do
	    x <- toConcrete x
	    bindToConcrete args $ \args ->
		ret [ foldl AppP (C.IdentP x) $ concatArgs args ]
    bindToConcrete (DefP i x args) ret =
	bracketP (appBrackets' args) ret $ \ret -> do
	    x <- toConcrete x
	    bindToConcrete args $ \args ->
		ret [ foldl AppP (C.IdentP x) $ concatArgs args ]
    bindToConcrete (A.AsP i x p)   ret = bindToConcreteCtx ArgumentCtx (x,p) $ \ (x,p) ->
					    ret $ map (C.AsP (getRange i) x) p
    bindToConcrete (A.AbsurdP i)   ret = ret [ C.AbsurdP (getRange i) ]
    bindToConcrete (A.LitP l)	   ret = ret [ C.LitP l ]
    bindToConcrete (A.DotP i e)	   ret = do
	e <- toConcreteCtx ArgumentCtx e
	ret [ C.DotP (getRange i) e ]
    bindToConcrete (A.ImplicitP i) ret = ret []

-- Helpers for recovering C.OpApp ------------------------------------------

tryToRecoverOpApp :: A.Expr -> AbsToCon C.Expr -> AbsToCon C.Expr
tryToRecoverOpApp e mdefault = case AV.appView e of
  NonApplication _ -> mdefault
  Application hd args -> do
    let  args' = [namedThing e | Arg NotHidden e <- args]
    case hd of
      HeadVar i n  -> doCName i (nameConcrete n) args'
      HeadDef i qn -> doQName i qn args'
      HeadCon i qn -> doQName i qn args'
  where

  -- qualified names can't use mixfix syntax
  doQName i qn as = case qnameToConcrete qn of	  -- TODO!!
    C.QName cn	-> doCName i cn as
    _		-> mdefault

  -- fall-back (wrong number of arguments or no holes)
  doCName i cn@(C.Name _ xs) es
    | length es /= numHoles = mdefault
    | List.null es	    = mdefault
    where numHoles = length [ () | Hole <- xs ]
	  msg = "doCName " ++ showList xs "" ++ " on " ++ show (length es) ++ " args"

  -- binary case
  doCName i cn@(C.Name _ xs) as
    | Hole <- head xs
    , Hole <- last xs = do
	let fixity = nameFixity i
	    a1	   = head as
	    an	   = last as
	    as'	   = init $ tail as
	e1 <- toConcreteCtx (LeftOperandCtx fixity) a1
	es <- mapM (toConcreteCtx InsideOperandCtx) as'
	en <- toConcreteCtx (RightOperandCtx fixity) an
	bracket (opBrackets fixity)
	    $ return $ OpApp (getRange (e1,en)) cn ([e1] ++ es ++ [en])

  -- prefix
  doCName i cn@(C.Name _ xs) as
    | Hole <- last xs = do
	let fixity = nameFixity i
	    an	   = last as
	    as'	   = init as
	es <- mapM (toConcreteCtx InsideOperandCtx) as'
	en <- toConcreteCtx (RightOperandCtx fixity) an
	bracket (opBrackets fixity)
	    $ return $ OpApp (getRange (cn,en)) cn (es ++ [en])

  -- postfix
  doCName i cn@(C.Name _ xs) as
    | Hole <- head xs = do
	let fixity = nameFixity i
	    a1	   = head as
	    as'	   = tail as
	e1 <- toConcreteCtx (LeftOperandCtx fixity) a1
	es <- mapM (toConcreteCtx InsideOperandCtx) as'
	bracket (opBrackets fixity)
	    $ return $ OpApp (getRange (e1,cn)) cn ([e1] ++ es)

  -- roundfix
  doCName i cn as = do
    es <- mapM (toConcreteCtx InsideOperandCtx) as
    return $ OpApp (getRange cn) cn es

