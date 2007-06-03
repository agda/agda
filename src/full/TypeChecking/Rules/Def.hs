{-# OPTIONS -cpp #-}

module TypeChecking.Rules.Def where

import Prelude hiding (mapM)
import Control.Applicative
import Control.Monad.State hiding (mapM)
import Control.Monad.Reader hiding (mapM)
import Control.Monad hiding (mapM)
import Data.List hiding (sort)
import Data.Traversable
import Data.Set (Set)
import qualified Data.Set as Set

import Syntax.Common
import Syntax.Position
import qualified Syntax.Abstract as A
import Syntax.Internal
import qualified Syntax.Info as Info
import qualified Syntax.Abstract.Pretty as A
import Syntax.Fixity

import TypeChecking.Monad
import TypeChecking.Reduce
import TypeChecking.Pretty
import TypeChecking.Substitute
import TypeChecking.Free
import TypeChecking.Constraints
import TypeChecking.Conversion
import TypeChecking.Empty
import TypeChecking.MetaVars
import TypeChecking.Patterns.Monad
import TypeChecking.Rebind
import TypeChecking.Primitive
import TypeChecking.With

import TypeChecking.Rules.Term		      ( checkExpr, inferExpr, checkTelescope )
import TypeChecking.Rules.LHS		      ( checkLeftHandSide )
import {-# SOURCE #-} TypeChecking.Rules.Decl ( checkDecls )

import Utils.Tuple
import Utils.Size
import Utils.Function
import Utils.List
import Utils.Permutation

#include "../../undefined.h"

---------------------------------------------------------------------------
-- * Definitions by pattern matching
---------------------------------------------------------------------------

-- | Type check a definition by pattern matching.
checkFunDef :: Info.DefInfo -> QName -> [A.Clause] -> TCM ()
checkFunDef i name cs =

    traceCall (CheckFunDef (getRange i) (qnameName name) cs) $ do   -- TODO!! (qnameName)
	-- Get the type of the function
	t    <- typeOfConst name

	reportSDoc "tc.def.fun" 10 $
	  sep [ text "checking body of" <+> prettyTCM name
	      , nest 2 $ text ":" <+> prettyTCM t
	      , nest 2 $ text "full type:" <+> (prettyTCM . defType =<< getConstInfo name)
	      ]

	-- Check the clauses
	cs <- mapM (checkClause t) cs

	-- Check that all clauses have the same number of arguments
	unless (allEqual $ map npats cs) $ typeError DifferentArities

	-- Annotate the clauses with which arguments are actually used.
	cs <- mapM rebindClause cs

	-- Add the definition
	addConstant name $ Defn name t (defaultDisplayForm name) $ Function cs $ Info.defAbstract i
	verbose 10 $ do
	  dx <- prettyTCM name
	  t' <- prettyTCM . defType =<< getConstInfo name
	  liftIO $ putStrLn $ "added " ++ show dx ++ " : " ++ show t'
    where
	npats (Clause ps _) = size ps

data WithFunctionProblem
      = NoWithFunction
      | WithFunction QName QName Telescope Telescope [Type] Type [Arg Pattern] Permutation [A.Clause]

-- | Type check a function clause.
checkClause :: Type -> A.Clause -> TCM Clause
checkClause t c@(A.Clause (A.LHS i x aps []) rhs wh) =
    traceCall (CheckClause t c) $
    checkLeftHandSide aps t $ \gamma delta sub xs ps t' perm -> do
      let mkBody v = foldr (\x t -> Bind $ Abs x t) (Body $ substs sub v) xs
      (body, with) <- checkWhere (size delta) wh $ 
	      case rhs of
		A.RHS e -> do
		  v <- checkExpr e t'
		  return (mkBody v, NoWithFunction)
		A.AbsurdRHS
		  | any (containsAbsurdPattern . namedThing . unArg) aps
			      -> return (NoBody, NoWithFunction)
		  | otherwise -> typeError $ NoRHSRequiresAbsurdPattern aps
		A.WithRHS es cs -> do

		  -- Infer the types of the with expressions
		  vas <- mapM inferExpr es
		  let (vs, as) = unzip vas

		  -- Invent a clever name for the with function
		  m <- currentModule
		  reportSDoc "tc.with.top" 20 $ text "with function module:" <+> prettyList (map prettyTCM $ mnameToList m)
		  aux <- qualify m <$> freshName_ "aux"

		  -- Create the body of the original function
		  ctx <- getContextTelescope
		  let n	   = size ctx
		      us   = [ Arg h (Var i []) | (i, Arg h _) <- zip [n - 1,n - 2..0] $ telToList ctx ]
		      v	   = substs sub $ Def aux $ us ++ (map (Arg NotHidden) vs)

		  reportSDoc "tc.with.top" 20 $ vcat
		    [ text "    with arguments" <+> prettyList (map prettyTCM vs)
		    , text "             types" <+> prettyList (map prettyTCM as)
		    , text "with function call" <+> prettyTCM (substs sub v)
		    , text "           context" <+> (prettyTCM =<< getContextTelescope)
		    ]

		  return (mkBody v, WithFunction x aux gamma delta as t' ps perm cs)
      escapeContext (size delta) $ checkWithFunction with
      return $ Clause ps body
checkClause t (A.Clause (A.LHS _ _ _ ps@(_ : _)) _ _) = typeError $ UnexpectedWithPatterns ps

checkWithFunction :: WithFunctionProblem -> TCM ()
checkWithFunction NoWithFunction = return ()
checkWithFunction (WithFunction f aux gamma delta as b qs perm cs) = do

  reportSDoc "tc.with.top" 10 $ vcat
    [ text "checkWithFunction"
    , nest 2 $ vcat
      [ text "delta =" <+> prettyTCM delta
      , text "gamma =" <+> prettyTCM gamma
      , text "as    =" <+> prettyList (map prettyTCM as)
      , text "b     =" <+> prettyTCM b
      ]
    ]

  -- Add the type of the auxiliary function to the signature
  df <- withDisplayForm f aux delta (size as) qs perm

  let auxType = telePi delta $ foldr fun b as
  case df of
    NoDisplay -> reportSDoc "tc.with.top" 20 $ text "NoDisplay"
    Display n ts dt -> reportSDoc "tc.with.top" 20 $ text "Display" <+> fsep
      [ text (show n)
      , prettyList $ map prettyTCM ts
      , prettyTCM dt
      ]
  addConstant aux (Defn aux auxType df Axiom)
  reportSDoc "tc.with.top" 10 $ sep
    [ text "added with function" <+> (prettyTCM aux) <+> text "of type"
    , nest 2 $ prettyTCM auxType
    , nest 2 $ text "-|" <+> (prettyTCM =<< getContextTelescope)
    ]

  -- Construct the body for the with function
  cs <- buildWithFunction aux gamma qs perm (size as) cs

  -- Check the with function
  checkFunDef info aux cs

  where
    fun a b = El s $ Fun (Arg NotHidden a) b
      where s = (sLub `on` getSort) a b
    info = Info.mkRangedDefInfo (nameConcrete $ qnameName aux) defaultFixity PublicAccess ConcreteDef (getRange cs)

-- | Type check a where clause. The first argument is the number of variables
--   bound in the left hand side.
checkWhere :: Int -> [A.Declaration] -> TCM a -> TCM a
checkWhere _ []			     ret = ret
checkWhere n [A.ScopedDecl scope ds] ret = withScope_ scope $ checkWhere n ds ret
checkWhere n [A.Section _ m tel ds]  ret = do
  checkTelescope tel $ \tel' -> do
    reportSDoc "tc.def.where" 10 $
      text "adding section:" <+> prettyTCM m <+> text (show (size tel')) <+> text (show n)
    addSection m (size tel' + n)  -- the variables bound in the lhs
				  -- are also parameters
    verboseS "tc.def.where" 10 $ do
      dx   <- prettyTCM m
      dtel <- mapM prettyA tel
      dtel' <- prettyTCM =<< lookupSection m
      liftIO $ putStrLn $ "checking where section " ++ show dx ++ " " ++ show dtel
      liftIO $ putStrLn $ "	   actual tele: " ++ show dtel'
    x <- withCurrentModule m $ checkDecls ds >> ret
    return x
checkWhere _ _ _ = __IMPOSSIBLE__

-- | Check if a pattern contains an absurd pattern. For instance, @suc ()@
containsAbsurdPattern :: A.Pattern -> Bool
containsAbsurdPattern p = case p of
    A.AbsurdP _   -> True
    A.VarP _	  -> False
    A.WildP _	  -> False
    A.ImplicitP _ -> False
    A.DotP _ _	  -> False
    A.LitP _	  -> False
    A.AsP _ _ p   -> containsAbsurdPattern p
    A.ConP _ _ ps -> any (containsAbsurdPattern . namedThing . unArg) ps
    A.DefP _ _ _  -> __IMPOSSIBLE__

{-
-- | Type check a left-hand side.
checkLHS :: [NamedArg A.Pattern] -> Type -> ([Term] -> [String] -> [Arg Pattern] -> Type -> TCM a) -> TCM a
checkLHS ps t ret = do

    verbose 15 $ do
      dt  <- prettyTCM t
      dps <- mapM prettyA ps
      liftIO $ putStrLn $ "checking clause " ++ show dps ++ " : " ++ show dt

    -- Save the state for later. (should this be done with the undo monad, or
    -- would that interfere with normal undo?)
    rollback <- do
	st  <- get
	env <- ask
	return $ \k -> do put st; local (const env) k

    -- Preliminary type checking to decide what should be variables and what
    -- should be dotted. Ignore empty types.
    runCheckPatM (checkPatterns ps t) $ \xs metas _ (ps0, ps, ts, a) -> do

    -- Build the new pattern, turning implicit patterns into variables when
    -- they couldn't be solved.
    ps1 <- evalStateT (buildNewPatterns ps0) metas

    verbose 10 $ do
	d0 <- A.showA ps0
	d1 <- A.showA ps1
	liftIO $ do
	putStrLn $ "first check"
	putStrLn $ "  xs    = " ++ show xs
	putStrLn $ "  metas = " ++ show metas
	putStrLn $ "  ps0   = " ++ d0
	putStrLn $ "  ps1   = " ++ d1

    verbose 10 $ do
	is <- mapM (instantiateFull . flip MetaV []) metas
	ds <- mapM prettyTCM is
	dts <- mapM prettyTCM =<< mapM instantiateFull ts
	liftIO $ putStrLn $ "  is    = " ++ concat (intersperse ", " $ map show ds)
	liftIO $ putStrLn $ "  ts    = " ++ concat (intersperse ", " $ map show dts)

    -- Now we forget that we ever type checked anything and type check the new
    -- pattern.
    rollback $ runCheckPatM (checkPatterns ps1 t)
	     $ \xs metas emptyTypes (_, ps, ts, a) -> do

    -- Check that the empty types are indeed empty
    mapM_ isEmptyType emptyTypes

    verbose 10 $ liftIO $ do
	putStrLn $ "second check"
	putStrLn $ "  xs    = " ++ show xs
	putStrLn $ "  metas = " ++ show metas

    verbose 10 $ do
	is <- mapM (instantiateFull . flip MetaV []) metas
	ds <- mapM prettyTCM is
	liftIO $ putStrLn $ "  is    = " ++ concat (intersperse ", " $ map show ds)

    -- Finally we type check the dot patterns and check that they match their
    -- instantiations.
    evalStateT (checkDotPatterns ps1) metas

    reportLn 15 "dot patterns check out"

    -- Sanity check. Make sure that all metas were instantiated.
    is <- mapM lookupMeta metas
    case [ getRange i | i <- is, FirstOrder <- [mvInstantiation i] ] of
	[] -> return ()
	rs -> fail $ "unsolved pattern metas at\n" ++ unlines (map show rs)

    -- Make sure to purge the type and the context from any first-order metas.
    a	 <- instantiateFull a
    flat <- instantiateFull =<< flatContext

    -- The context might not be well-formed. We may have to do some reordering.
    reportLn 20 $ "Before reordering:"
    verbose 20 $ dumpContext flat

    flat' <- reorderCtx flat

    -- Compute renamings to and from the new context
    let sub  = (computeSubst `on` map (fst . unArg)) flat flat'
	rsub = (computeSubst `on` map (fst . unArg)) flat' flat

    -- Apply the reordering to the types in the new context
    let flat'' = map (fmap $ id -*- substs sub) flat'

    reportLn 20 $ "After reordering:"
    verbose 20 $ dumpContext flat'

    -- Deflatten the context
    let ctx = mkContext flat''

    inContext ctx $ do

	verbose 20 $ do
	    d <- prettyTCM ctx
	    dt <- prettyTCM (substs sub a)
	    liftIO $ putStrLn $ "context = " ++ show d
	    liftIO $ putStrLn $ "type    = " ++ show dt

	reportLn 20 $ "finished type checking left hand side"
	ret rsub xs ps (substs sub a)
    where
	popMeta = do
	    x : xs <- get
	    put xs
	    return x

	buildNewPatterns :: [NamedArg A.Pattern] -> StateT [MetaId] TCM [NamedArg A.Pattern]
	buildNewPatterns = mapM buildNewPattern'

	buildNewPattern' = (traverse . traverse) buildNewPattern

	buildNewPattern :: A.Pattern -> StateT [MetaId] TCM A.Pattern
	buildNewPattern (A.ImplicitP i) = do
	    x <- popMeta
	    v <- lift $ instantiate (MetaV x [])
	    lift $ verbose 6 $ do
		d <- prettyTCM v
		liftIO $ putStrLn $ "new pattern for " ++ show x ++ " = " ++ show d
	    case v of
		-- Unsolved metas become variables
		MetaV y _ | x == y  -> return $ A.WildP i
		-- Anything else becomes dotted
		_		    -> do
		    lift $ verbose 6 $ do
			d <- prettyTCM =<< instantiateFull v
			liftIO $ putStrLn $ show x ++ " := " ++ show d
		    scope <- lift getScope
		    return $ A.DotP i (A.Underscore $ info scope)
		    where info s = Info.MetaInfo (getRange i) s Nothing

	buildNewPattern p@(A.VarP _)	= return p
	buildNewPattern p@(A.WildP _)	= return p
	buildNewPattern p@(A.DotP _ _)	= popMeta >> return p
	buildNewPattern (A.AsP i x p)	= A.AsP i x <$> buildNewPattern p
	buildNewPattern (A.ConP i c ps) = A.ConP i c <$> buildNewPatterns ps
	buildNewPattern (A.DefP i c ps) = A.DefP i c <$> buildNewPatterns ps
	buildNewPattern p@(A.AbsurdP _)	= return p
	buildNewPattern p@(A.LitP _)	= return p

	checkDotPatterns :: [NamedArg A.Pattern] -> StateT [MetaId] TCM ()
	checkDotPatterns = mapM_ checkDotPattern'

	checkDotPattern' p = (traverse . traverse) checkDotPattern p >> return ()

	checkDotPattern :: A.Pattern -> StateT [MetaId] TCM ()
	checkDotPattern (A.ImplicitP i) = __IMPOSSIBLE__    -- there should be no implicits left at this point
	checkDotPattern p@(A.VarP _)	= return ()
	checkDotPattern p@(A.WildP _)	= return ()
	checkDotPattern p@(A.DotP i e)	= do
	    x <- popMeta
	    lift $ do
		firstOrder <- isFirstOrder x    -- first order and uninstantiated
		when firstOrder $ typeError
				$ InternalError	-- TODO: proper error
				$ "uninstantiated dot pattern at " ++ show (getRange i)
		HasType _ o <- mvJudgement <$> lookupMeta x
		a <- getOpen o
		v <- checkExpr e a
		noConstraints $ equalTerm t v (MetaV x [])
	checkDotPattern (A.AsP i x p)	= checkDotPattern p
	checkDotPattern (A.ConP i c ps) = checkDotPatterns ps
	checkDotPattern (A.DefP i c ps) = checkDotPatterns ps
	checkDotPattern p@(A.AbsurdP _)	= return ()
	checkDotPattern p@(A.LitP _)	= return ()

	-- Get the flattened context
	flatContext :: TCM Context
	flatContext = do
	    n <- size <$> getContext
	    mapM f [0..n - 1]
	    where
		f i = do
		    Arg h t <- instantiateFull =<< typeOfBV' i
		    x <- nameOfBV i
		    return $ Arg h (x, t)

	-- Reorder a flat context to make sure it's valid.
	reorderCtx :: Context -> TCM Context
	reorderCtx ctx = reverse <$> reorder (reverse ctx)
	    where
		free t = mapM nameOfBV (Set.toList $ allVars $ freeVars t)

		reorder :: [Arg (Name, Type)] -> TCM [Arg (Name, Type)]
		reorder []	      = return []
		reorder (Arg h (x,t) : tel) = do
		    tel' <- reorder tel
		    xs   <- free t
		    verbose 20 $ do
			d <- prettyTCM t
			liftIO $ putStrLn $ "freeIn " ++ show x ++ " : " ++ show d ++ " are " ++ show xs
		    case intersect (map (fst . unArg) tel') xs of
			[] -> return $ Arg h (x,t) : tel'
			zs -> return $ ins zs (Arg h (x,t)) tel'

		ins [] p tel		   = p : tel
		ins xs p (Arg h (x,t):tel) = Arg h (x,t) : ins (delete x xs) p tel
		ins (_:_) _ []		   = __IMPOSSIBLE__

	-- Compute a renaming from the first names to the second.
	computeSubst :: [Name] -> [Name] -> [Term]
	computeSubst old new = map ix old
	    where
		ix x = case findIndex (==x) new of
			Just i	-> Var i []
			Nothing	-> __IMPOSSIBLE__

	-- Take a flat (but valid) context and turn it into a proper context.
	mkContext :: [Arg (Name, Type)] -> Context
	mkContext = reverse . mkCtx . reverse
	    where
		mkCtx []	  = []
		mkCtx ctx0@(Arg h (x,t) : ctx) = Arg h (x, substs sub t) : mkCtx ctx
		    where
			sub = map err ctx0 ++ [ Var i [] | i <- [0..] ]

			err (Arg _ (y,_)) = error $ show y ++ " occurs in the type of " ++ show x

	-- Print a flat context
	dumpContext :: Context -> TCM ()
	dumpContext ctx = do
	    let pr (Arg h (x,t)) = do
		  d <- prettyTCM t
		  return $ "  " ++ par h (show x ++ " : " ++ show d)
		par Hidden    s = "{" ++ s ++ "}"
		par NotHidden s = "(" ++ s ++ ")"
	    ds <- mapM pr ctx
	    liftIO $ putStr $ unlines $ reverse ds
-}

actualConstructor :: MonadTCM tcm => QName -> tcm QName
actualConstructor c = do
    v <- constructorForm =<< normalise (Con c [])
    case ignoreBlocking v of
	Con c _	-> return c
	_	-> actualConstructor =<< stripLambdas v
    where
	stripLambdas v = case ignoreBlocking v of
	    Con c _ -> return c
	    Lam h b -> do
		x <- freshName_ $ absName b
		addCtx x (Arg h $ sort Prop) $ stripLambdas (absBody b)
	    _	    -> typeError $ GenericError $ "Not a constructor: " ++ show c

