{-# LANGUAGE CPP #-}

module Agda.TypeChecking.Rules.Def where

import Prelude hiding (mapM)
import Control.Applicative
import Control.Monad.State hiding (mapM)
import Control.Monad.Reader hiding (mapM)
import Control.Monad hiding (mapM)
import Data.List hiding (sort)
import Data.Traversable
import Data.Set (Set)
import qualified Data.Set as Set
import qualified Agda.Utils.IO.Locale as LocIO

import Agda.Syntax.Common
import Agda.Syntax.Position
import qualified Agda.Syntax.Abstract as A
import Agda.Syntax.Internal
import qualified Agda.Syntax.Info as Info
import qualified Agda.Syntax.Abstract.Pretty as A
import Agda.Syntax.Fixity
import Agda.Syntax.Translation.InternalToAbstract
import Agda.Syntax.Info
import Agda.Syntax.Scope.Base (emptyScopeInfo)
import Agda.TypeChecking.Monad
import Agda.TypeChecking.Monad.Builtin (primRefl, primEquality)
import Agda.TypeChecking.Reduce
import Agda.TypeChecking.Pretty
import Agda.TypeChecking.Substitute
import Agda.TypeChecking.Free
import Agda.TypeChecking.Constraints
import Agda.TypeChecking.Conversion
import Agda.TypeChecking.Empty
import Agda.TypeChecking.MetaVars
import Agda.TypeChecking.Rebind
import Agda.TypeChecking.Primitive hiding (Nat)
import Agda.TypeChecking.With
import Agda.TypeChecking.Telescope
import Agda.TypeChecking.Coverage
import Agda.TypeChecking.Injectivity
import Agda.TypeChecking.Polarity
import Agda.TypeChecking.Irrelevance
import Agda.TypeChecking.SizedTypes
import Agda.TypeChecking.CompiledClause.Compile

import Agda.TypeChecking.Rules.Term                ( checkExpr, inferExpr, checkTelescope_, isType_ )
import Agda.TypeChecking.Rules.LHS                 ( checkLeftHandSide )
import {-# SOURCE #-} Agda.TypeChecking.Rules.Decl ( checkDecls )
import Agda.TypeChecking.Rules.Data                ( isCoinductive )

import Agda.Interaction.Options

import Agda.Utils.Tuple
import Agda.Utils.Size
import Agda.Utils.Function
import Agda.Utils.List
import Agda.Utils.Permutation
import Agda.Utils.Monad

#include "../../undefined.h"
import Agda.Utils.Impossible

---------------------------------------------------------------------------
-- * Definitions by pattern matching
---------------------------------------------------------------------------

checkFunDef :: Delayed -> Info.DefInfo -> QName -> [A.Clause] -> TCM ()
checkFunDef delayed i name cs = do
        -- Get the type and relevance of the function
        t    <- typeOfConst name
        rel  <- relOfConst name
        checkFunDef' t rel delayed i name cs

-- | Type check a definition by pattern matching. The first argument
-- specifies whether the clauses are delayed or not.
checkFunDef' :: Type -> Relevance -> Delayed -> Info.DefInfo -> QName -> [A.Clause] -> TCM ()
checkFunDef' t rel delayed i name cs =

    traceCall (CheckFunDef (getRange i) (qnameName name) cs) $ do   -- TODO!! (qnameName)
        reportSDoc "tc.def.fun" 10 $
          sep [ text "checking body of" <+> prettyTCM name
              , nest 2 $ text ":" <+> prettyTCM t
              , nest 2 $ text "full type:" <+> (prettyTCM . defType =<< getConstInfo name)
              ]

        -- Check the clauses
        let check c = do
              c <- applyRelevanceToContext rel $ checkClause t c
              solveSizeConstraints
              return c
        cs <- mapM check cs

        -- Check that all clauses have the same number of arguments
        unless (allEqual $ map npats cs) $ typeError DifferentArities

        reportSDoc "tc.cc" 15 $ do
          sep [ text "clauses before rebindClause"
              , nest 2 $ prettyTCM (map (NamedClause name) cs)
              ]

        -- Annotate the clauses with which arguments are actually used.
        cs <- instantiateFull =<< mapM rebindClause cs
        -- Andreas, 2010-11-12
        -- rebindClause is the identity, and instantiateFull eta-contracts
        -- removing this eta-contraction fixes issue 361
        -- however, Data.Star.Decoration.gmapAll no longer type-checks
        -- possibly due to missing eta-contraction!?

        -- Check if the function is injective
        inv <- checkInjectivity name cs

        reportSDoc "tc.cc" 15 $ do
          sep [ text "clauses before compilation"
              , nest 2 $ prettyTCM (map (NamedClause name) cs)
              ]

        -- Compile the clauses
        cc <- compileClauses True cs

        reportSDoc "tc.cc" 10 $ do
          sep [ text "compiled clauses of" <+> prettyTCM name
              , nest 2 $ text (show cc)
              ]

        -- Add the definition
        addConstant name $ Defn rel name t (defaultDisplayForm name) 0 noCompiledRep
                         $ Function
                            { funClauses        = cs
                            , funCompiled       = cc
                            , funDelayed        = delayed
                            , funInv            = inv
                            , funAbstr          = Info.defAbstract i
                            , funPolarity       = []
                            , funArgOccurrences = []
                            , funProjection     = Nothing
                            }
        computePolarity name
        reportSDoc "tc.def.fun" 10 $ do
          sep [ text "added " <+> prettyTCM name <+> text ":"
              , nest 2 $ prettyTCM . defType =<< getConstInfo name
              ]

        -- Check pattern coverage
        checkCoverage name

        reportSLn "tc.def.fun.compile" 10 $
          "compiled clauses for " ++ show name ++ ":\n" ++ show cc
    where
        npats = size . clausePats


-- | Insert some patterns in the in with-clauses LHS of the given RHS
insertPatterns :: [A.Pattern] -> A.RHS -> A.RHS
insertPatterns pats (A.WithRHS aux es cs) = A.WithRHS aux es (map insertToClause cs)
    where insertToClause (A.Clause (A.LHS i x aps ps) rhs ds)
--              = A.Clause (A.LHS i x (aps ++ map (Arg NotHidden . unnamed) pats) (ps)) (insertPatterns pats rhs) ds
              = A.Clause (A.LHS i x aps (pats ++ ps)) (insertPatterns pats rhs) ds
insertPatterns pats (A.RewriteRHS qs eqs rhs wh) = A.RewriteRHS qs eqs (insertPatterns pats rhs) wh
insertPatterns pats rhs = rhs


data WithFunctionProblem
      = NoWithFunction
      | WithFunction QName          -- parent function name
                     QName          -- with function name
                     Telescope      -- arguments to parent function
                     Telescope      -- arguments to the with function before the with expressions
                     Telescope      -- arguments to the with function after the with expressions
                     [Term]         -- with expressions
                     [Type]         -- types of the with expressions
                     Type           -- type of the right hand side
                     [Arg Pattern]  -- parent patterns
                     Permutation    -- permutation reordering the variables in the parent pattern
                     [A.Clause]     -- the given clauses for the with function

-- | Type check a function clause.
checkClause :: Type -> A.Clause -> TCM Clause
checkClause t c@(A.Clause (A.LHS i x aps []) rhs0 wh) =
    traceCall (CheckClause t c) $
    checkLeftHandSide c aps t $ \gamma delta sub xs ps t' perm -> do
      let mkBody v = foldr (\x t -> Bind $ Abs x t) (Body $ substs sub v) xs
      (body, with) <- checkWhere (size delta) wh $ let
          handleRHS rhs =
              case rhs of
                A.RHS e
                  | any (containsAbsurdPattern . namedThing . unArg) aps ->
                    typeError $ AbsurdPatternRequiresNoRHS aps
                  | otherwise -> do
                    v <- checkExpr e t'
                    return (mkBody v, NoWithFunction)
                A.AbsurdRHS
                  | any (containsAbsurdPattern . namedThing . unArg) aps
                              -> return (NoBody, NoWithFunction)
                  | otherwise -> typeError $ NoRHSRequiresAbsurdPattern aps
                A.RewriteRHS [] (_:_) _ _ -> __IMPOSSIBLE__
                A.RewriteRHS (_:_) [] _ _ -> __IMPOSSIBLE__
                A.RewriteRHS [] [] rhs [] -> handleRHS rhs
                A.RewriteRHS [] [] _ (_:_) -> __IMPOSSIBLE__
                A.RewriteRHS (qname:names) (eq:eqs) rhs wh -> do
                     (proof,t) <- inferExpr eq
                     t' <- reduce =<< instantiateFull t
                     equality <- primEquality >>= \eq -> return $ case eq of
                        Lam Hidden (Abs _ (Lam Hidden (Abs _ (Def equality _)))) -> equality
                        Lam Hidden (Abs _ (Def equality _))                      -> equality
                        Def equality _                                           -> equality
                        _                                                        -> __IMPOSSIBLE__
                     reflCon <- primRefl >>= \refl -> return $ case refl of
                         Con reflCon [] -> reflCon
                         _              -> __IMPOSSIBLE__
                     (rewriteType,rewriteFrom,rewriteTo) <- case t' of
                         El _Set0 (Def equality' [_level, Arg Hidden Relevant rewriteType,
                                                  Arg NotHidden Relevant rewriteFrom, Arg NotHidden Relevant rewriteTo])
                            | equality' == equality ->
                              return (rewriteType, rewriteFrom, rewriteTo)
                         _ -> do
                          err <- text "Cannot rewrite by equation of type" <+> prettyTCM t'
                          typeError $ GenericError $ show err

                     let info = PatRange noRange
                         metaInfo = Info.MetaInfo noRange emptyScopeInfo Nothing
                         underscore = A.Underscore metaInfo

                     [rewriteFromExpr,rewriteToExpr,rewriteTypeExpr, proofExpr] <-
                      disableDisplayForms $ setShowImplicitArguments True $ reify
                        [rewriteFrom,   rewriteTo,    rewriteType    , proof]
                     let (inner, outer) -- the where clauses should go on the inner-most with
                           | null eqs  = ([], wh)
                           | otherwise = (wh, [])
                         newRhs = A.WithRHS qname [rewriteFromExpr, proofExpr]
                                  [A.Clause (A.LHS i x aps pats)
                                    (A.RewriteRHS names eqs (insertPatterns pats rhs) inner)
                                    outer]
                         pats = [A.DotP info underscore, -- rewriteToExpr,
                                 A.ConP info (AmbQ [reflCon]) []]
                     reportSDoc "tc.rewrite.top" 25 $ vcat
                                         [ text "from = " <+> prettyTCM rewriteFromExpr,
                                           text "to = " <+> prettyTCM rewriteToExpr,
                                           text "typ = " <+> prettyTCM rewriteType,
                                           text "proof = " <+> prettyTCM proofExpr,
                                           text "equ = " <+> prettyTCM t' ]
                     handleRHS newRhs

                A.WithRHS aux es cs -> do
                  reportSDoc "tc.with.top" 5 $
                    text "TC.Rules.Def.checkclause reached A.WithRHS"
                  reportSDoc "tc.with.top" 30 $
                    text (show c)
                  -- Infer the types of the with expressions
                  vas <- mapM inferExpr es
                  (vs0, as) <- instantiateFull (unzip vas)
                  (vs, as)  <- normalise (vs0, as)

                  -- Invent a clever name for the with function
                  m <- currentModule
                  reportSDoc "tc.with.top" 20 $ text "with function module:" <+> prettyList (map prettyTCM $ mnameToList m)

                  -- Split the telescope into the part needed to type the with arguments
                  -- and all the other stuff
                  let fv = allVars $ freeVars (vs, as)
                      SplitTel delta1 delta2 perm' = splitTelescope fv delta
                      finalPerm = composeP perm' perm

                  reportSDoc "tc.with.top" 25 $ vcat
                    [ text "delta  =" <+> prettyTCM delta
                    , text "delta1 =" <+> prettyTCM delta1
                    , text "delta2 =" <+> addCtxTel delta1 (prettyTCM delta2)
                    , text "vs     =" <+> prettyTCM vs
                    , text "as     =" <+> prettyTCM as
                    ]

                  -- Create the body of the original function
                  ctx <- getContextTelescope
                  let n    = size ctx
                      m    = size delta
                      us   = [ Arg h r (Var i []) | (i, Arg h r _) <- zip [n - 1,n - 2..0] $ telToList ctx ]
                      (us0, us1') = genericSplitAt (n - m) us
                      (us1, us2)  = genericSplitAt (size delta1) $ permute perm' us1'
                      v    = Def aux $ us0 ++ us1 ++ (map defaultArg vs0) ++ us2

                  -- We need Δ₁Δ₂ ⊢ t'
                  t' <- return $ renameP (reverseP perm') t'
                  -- and Δ₁ ⊢ vs : as
                  (vs, as) <- do
                    let var = flip Var []
                        -- We know that as does not depend on Δ₂
                        rho = replicate (size delta2) __IMPOSSIBLE__ ++ map var [0..]
                    return $ substs rho $ renameP (reverseP perm') (vs, as)

                  reportSDoc "tc.with.top" 20 $ vcat
                    [ text "    with arguments" <+> prettyList (map prettyTCM vs)
                    , text "             types" <+> prettyList (map prettyTCM as)
                    , text "with function call" <+> prettyTCM v
                    , text "           context" <+> (prettyTCM =<< getContextTelescope)
                    , text "             delta" <+> prettyTCM delta
                    , text "                fv" <+> text (show fv)
                    , text "              body" <+> (addCtxTel delta $ prettyTCM $ mkBody v)
                    ]

                  return (mkBody v, WithFunction x aux gamma delta1 delta2 vs as t' ps finalPerm cs)
          in handleRHS rhs0
      escapeContext (size delta) $ checkWithFunction with

      reportSDoc "tc.lhs.top" 10 $ escapeContext (size delta) $ vcat
        [ text "Clause before translation:"
        , nest 2 $ vcat
          [ text "delta =" <+> prettyTCM delta
          , text "perm  =" <+> text (show perm)
          , text "ps    =" <+> text (show ps)
          , text "body  =" <+> text (show body)
          , text "body  =" <+> prettyTCM body
          ]
        ]

      return $
        Clause { clauseRange = getRange i
               , clauseTel   = killRange delta
               , clausePerm  = perm
               , clausePats  = ps
               , clauseBody  = body
               }

checkClause t (A.Clause (A.LHS _ _ _ ps@(_ : _)) _ _) = typeError $ UnexpectedWithPatterns ps

checkWithFunction :: WithFunctionProblem -> TCM ()
checkWithFunction NoWithFunction = return ()
checkWithFunction (WithFunction f aux gamma delta1 delta2 vs as b qs perm cs) = do

  reportSDoc "tc.with.top" 10 $ vcat
    [ text "checkWithFunction"
    , nest 2 $ vcat
      [ text "delta1 =" <+> prettyTCM delta1
      , text "delta2 =" <+> prettyTCM delta2
      , text "gamma  =" <+> prettyTCM gamma
      , text "as     =" <+> addCtxTel delta1 (prettyTCM as)
      , text "vs     =" <+> addCtxTel delta1 (prettyTCM vs)
      , text "b      =" <+> prettyTCM b
      , text "qs     =" <+> text (show qs)
      , text "perm   =" <+> text (show perm)
      ]
    ]

  -- Add the type of the auxiliary function to the signature

  -- With display forms are closed
  df <- makeClosed <$> withDisplayForm f aux delta1 delta2 (size as) qs perm

  reportSLn "tc.with.top" 20 "created with display form"

  -- Generate the type of the with function
  candidateType <- withFunctionType delta1 vs as delta2 b
  reportSDoc "tc.with.type" 10 $ sep [ text "candidate type:", nest 2 $ prettyTCM candidateType ]
  absAuxType <- setShowImplicitArguments True
                $ disableDisplayForms
                $ dontReifyInteractionPoints
                $ reify candidateType
  reportSDoc "tc.with.top" 15 $
    vcat [ text "type of with function:"
         , nest 2 $ prettyTCM absAuxType
         ]
  -- The ranges in the generated type are completely bogus, so we kill them.
  auxType <- setCurrentRange (getRange cs) $ isType_ $ killRange absAuxType

  case df of
    OpenThing _ (Display n ts dt) -> reportSDoc "tc.with.top" 20 $ text "Display" <+> fsep
      [ text (show n)
      , prettyList $ map prettyTCM ts
      , prettyTCM dt
      ]
  addConstant aux (Defn Relevant aux auxType [df] 0 noCompiledRep Axiom)
  solveSizeConstraints

  reportSDoc "tc.with.top" 10 $ sep
    [ text "added with function" <+> (prettyTCM aux) <+> text "of type"
    , nest 2 $ prettyTCM auxType
    , nest 2 $ text "-|" <+> (prettyTCM =<< getContextTelescope)
    ]

  -- Construct the body for the with function
  cs <- buildWithFunction aux gamma qs perm (size delta1) (size as) cs

  -- Check the with function
  checkFunDef NotDelayed info aux cs

  where
    info = Info.mkDefInfo (nameConcrete $ qnameName aux) defaultFixity' PublicAccess ConcreteDef (getRange cs)

-- | Type check a where clause. The first argument is the number of variables
--   bound in the left hand side.
checkWhere :: Nat -> [A.Declaration] -> TCM a -> TCM a
checkWhere _ []                      ret = ret
checkWhere n [A.ScopedDecl scope ds] ret = withScope_ scope $ checkWhere n ds ret
checkWhere n [A.Section _ m tel ds]  ret = do
  checkTelescope_ tel $ \tel' -> do
    reportSDoc "tc.def.where" 10 $
      text "adding section:" <+> prettyTCM m <+> text (show (size tel')) <+> text (show n)
    addSection m (size tel' + n)  -- the variables bound in the lhs
                                  -- are also parameters
    verboseS "tc.def.where" 10 $ do
      dx   <- prettyTCM m
      dtel <- mapM prettyA tel
      dtel' <- prettyTCM =<< lookupSection m
      liftIO $ LocIO.putStrLn $ "checking where section " ++ show dx ++ " " ++ show dtel
      liftIO $ LocIO.putStrLn $ "        actual tele: " ++ show dtel'
    x <- withCurrentModule m $ checkDecls ds >> ret
    return x
checkWhere _ _ _ = __IMPOSSIBLE__

-- | Check if a pattern contains an absurd pattern. For instance, @suc ()@
containsAbsurdPattern :: A.Pattern -> Bool
containsAbsurdPattern p = case p of
    A.AbsurdP _   -> True
    A.VarP _      -> False
    A.WildP _     -> False
    A.ImplicitP _ -> False
    A.DotP _ _    -> False
    A.LitP _      -> False
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
      liftIO $ LocIO.putStrLn $ "checking clause " ++ show dps ++ " : " ++ show dt

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
        LocIO.putStrLn $ "first check"
        LocIO.putStrLn $ "  xs    = " ++ show xs
        LocIO.putStrLn $ "  metas = " ++ show metas
        LocIO.putStrLn $ "  ps0   = " ++ d0
        LocIO.putStrLn $ "  ps1   = " ++ d1

    verbose 10 $ do
        is <- mapM (instantiateFull . flip MetaV []) metas
        ds <- mapM prettyTCM is
        dts <- mapM prettyTCM =<< mapM instantiateFull ts
        liftIO $ LocIO.putStrLn $ "  is    = " ++ concat (intersperse ", " $ map show ds)
        liftIO $ LocIO.putStrLn $ "  ts    = " ++ concat (intersperse ", " $ map show dts)

    -- Now we forget that we ever type checked anything and type check the new
    -- pattern.
    rollback $ runCheckPatM (checkPatterns ps1 t)
             $ \xs metas emptyTypes (_, ps, ts, a) -> do

    -- Check that the empty types are indeed empty
    mapM_ isEmptyType emptyTypes

    verbose 10 $ liftIO $ do
        LocIO.putStrLn $ "second check"
        LocIO.putStrLn $ "  xs    = " ++ show xs
        LocIO.putStrLn $ "  metas = " ++ show metas

    verbose 10 $ do
        is <- mapM (instantiateFull . flip MetaV []) metas
        ds <- mapM prettyTCM is
        liftIO $ LocIO.putStrLn $ "  is    = " ++ concat (intersperse ", " $ map show ds)

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
    a    <- instantiateFull a
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
            liftIO $ LocIO.putStrLn $ "context = " ++ show d
            liftIO $ LocIO.putStrLn $ "type    = " ++ show dt

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
                liftIO $ LocIO.putStrLn $ "new pattern for " ++ show x ++ " = " ++ show d
            case v of
                -- Unsolved metas become variables
                MetaV y _ | x == y  -> return $ A.WildP i
                -- Anything else becomes dotted
                _                   -> do
                    lift $ verbose 6 $ do
                        d <- prettyTCM =<< instantiateFull v
                        liftIO $ LocIO.putStrLn $ show x ++ " := " ++ show d
                    scope <- lift getScope
                    return $ A.DotP i (A.Underscore $ info scope)
                    where info s = Info.MetaInfo (getRange i) s Nothing

        buildNewPattern p@(A.VarP _)    = return p
        buildNewPattern p@(A.WildP _)   = return p
        buildNewPattern p@(A.DotP _ _)  = popMeta >> return p
        buildNewPattern (A.AsP i x p)   = A.AsP i x <$> buildNewPattern p
        buildNewPattern (A.ConP i c ps) = A.ConP i c <$> buildNewPatterns ps
        buildNewPattern (A.DefP i c ps) = A.DefP i c <$> buildNewPatterns ps
        buildNewPattern p@(A.AbsurdP _) = return p
        buildNewPattern p@(A.LitP _)    = return p

        checkDotPatterns :: [NamedArg A.Pattern] -> StateT [MetaId] TCM ()
        checkDotPatterns = mapM_ checkDotPattern'

        checkDotPattern' p = (traverse . traverse) checkDotPattern p >> return ()

        checkDotPattern :: A.Pattern -> StateT [MetaId] TCM ()
        checkDotPattern (A.ImplicitP i) = __IMPOSSIBLE__    -- there should be no implicits left at this point
        checkDotPattern p@(A.VarP _)    = return ()
        checkDotPattern p@(A.WildP _)   = return ()
        checkDotPattern p@(A.DotP i e)  = do
            x <- popMeta
            lift $ do
                firstOrder <- isFirstOrder x    -- first order and uninstantiated
                when firstOrder $ typeError
                                $ InternalError -- TODO: proper error
                                $ "uninstantiated dot pattern at " ++ show (getRange i)
                HasType _ o <- mvJudgement <$> lookupMeta x
                a <- getOpen o
                v <- checkExpr e a
                noConstraints $ equalTerm t v (MetaV x [])
        checkDotPattern (A.AsP i x p)   = checkDotPattern p
        checkDotPattern (A.ConP i c ps) = checkDotPatterns ps
        checkDotPattern (A.DefP i c ps) = checkDotPatterns ps
        checkDotPattern p@(A.AbsurdP _) = return ()
        checkDotPattern p@(A.LitP _)    = return ()

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
                reorder []            = return []
                reorder (Arg h (x,t) : tel) = do
                    tel' <- reorder tel
                    xs   <- free t
                    verbose 20 $ do
                        d <- prettyTCM t
                        liftIO $ LocIO.putStrLn $ "freeIn " ++ show x ++ " : " ++ show d ++ " are " ++ show xs
                    case intersect (map (fst . unArg) tel') xs of
                        [] -> return $ Arg h (x,t) : tel'
                        zs -> return $ ins zs (Arg h (x,t)) tel'

                ins [] p tel               = p : tel
                ins xs p (Arg h (x,t):tel) = Arg h (x,t) : ins (delete x xs) p tel
                ins (_:_) _ []             = __IMPOSSIBLE__

        -- Compute a renaming from the first names to the second.
        computeSubst :: [Name] -> [Name] -> [Term]
        computeSubst old new = map ix old
            where
                ix x = case findIndex (==x) new of
                        Just i  -> Var i []
                        Nothing -> __IMPOSSIBLE__

        -- Take a flat (but valid) context and turn it into a proper context.
        mkContext :: [Arg (Name, Type)] -> Context
        mkContext = reverse . mkCtx . reverse
            where
                mkCtx []          = []
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
            liftIO $ LocIO.putStr $ unlines $ reverse ds
-}

actualConstructor :: MonadTCM tcm => QName -> tcm QName
actualConstructor c = do
    v <- constructorForm =<< normalise (Con c [])
    case v of
        Con c _ -> return c
        _       -> actualConstructor =<< stripLambdas v
    where
        stripLambdas v = case v of
            Con c _ -> return c
            Lam h b -> do
                x <- freshName_ $ absName b
                addCtx x (Arg h Relevant $ sort Prop) $ stripLambdas (absBody b)
            _       -> typeError $ GenericError $ "Not a constructor: " ++ show c
