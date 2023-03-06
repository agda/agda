{-# LANGUAGE NondecreasingIndentation #-}

module Agda.Interaction.MakeCase where

import Prelude hiding ((!!), null)

import Control.Monad

import Data.Either
import Data.Function (on)
import qualified Data.List as List
import Data.Maybe
import Data.Monoid

import Agda.Syntax.Common
import Agda.Syntax.Info
import Agda.Syntax.Position
import Agda.Syntax.Concrete (NameInScope(..))
import qualified Agda.Syntax.Concrete as C
import qualified Agda.Syntax.Concrete.Pattern as C
import qualified Agda.Syntax.Abstract as A
import qualified Agda.Syntax.Abstract.Pattern as A
import Agda.Syntax.Internal
import Agda.Syntax.Internal.Pattern
import Agda.Syntax.Scope.Base  ( ResolvedName(..), BindingSource(..), KindOfName(..), exceptKindsOfNames )
import Agda.Syntax.Scope.Monad ( resolveName' )
import Agda.Syntax.Translation.InternalToAbstract

import Agda.TypeChecking.Monad
import Agda.TypeChecking.Coverage
import Agda.TypeChecking.Coverage.Match ( SplitPatVar(..) , SplitPattern , applySplitPSubst , fromSplitPatterns )
import Agda.TypeChecking.Empty ( isEmptyTel )
import Agda.TypeChecking.Pretty
import Agda.TypeChecking.Reduce
import Agda.TypeChecking.Rules.Def (checkClauseLHS)
import Agda.TypeChecking.Rules.LHS (LHSResult(..))
import Agda.TypeChecking.Rules.LHS.Problem (AsBinding(..))

import Agda.Interaction.Options
import Agda.Interaction.BasicOps

import qualified Agda.Utils.BiMap as BiMap
import Agda.Utils.Function
import Agda.Utils.Functor
import Agda.Utils.List
import Agda.Utils.Monad
import Agda.Utils.Null
import Agda.Utils.Pretty (prettyShow)
import qualified Agda.Utils.Pretty as P
import Agda.Utils.Size

import Agda.Utils.Impossible

type CaseContext = Maybe ExtLamInfo

-- | Parse variables (visible or hidden), returning their de Bruijn indices.
--   Used in 'makeCase'.

parseVariables
  :: QName           -- ^ The function name.
  -> Context         -- ^ The context of the RHS of the clause we are splitting.
  -> [AsBinding]     -- ^ The as-bindings of the clause we are splitting
  -> InteractionId   -- ^ The hole of this function we are working on.
  -> Range           -- ^ The range of this hole.
  -> [String]        -- ^ The words the user entered in this hole (variable names).
  -> TCM [(Int,NameInScope)] -- ^ The computed de Bruijn indices of the variables to split on,
                             --   with information about whether each variable is in scope.
parseVariables f cxt asb ii rng ss = do

  -- We parse the variables in two steps:
  -- (1) Convert the strings given by the user to abstract names,
  --     using the scope information from the interaction meta.
  -- (2) Convert the abstract names to de Bruijn indices,
  --     using the context of the clause.

  -- Get into the context of the meta.
  mId <- lookupInteractionId ii
  updateMetaVarRange mId rng
  mi  <- getMetaInfo <$> lookupLocalMeta mId
  enterClosure mi $ \ r -> do

  reportSDoc "interaction.case" 20 $ do
    m   <- currentModule
    tel <- lookupSection m
    vcat
     [ "parseVariables:"
     , "current module  =" <+> prettyTCM m
     , "current section =" <+> inTopContext (prettyTCM tel)
     , "clause context  =" <+> prettyTCM (PrettyContext cxt)
     ]

  -- Get printed representation of variables in context.  These are
  -- used for recognizing when the user wants to make a hidden
  -- variable (which is not in scope) visible.
  n  <- getContextSize
  xs <- forM (downFrom n) $ \ i ->
    (,) <$> (P.render <$> prettyTCM (var i)) <*> nameOfBV i

  -- Step 1: From strings to abstract names
  abstractNames :: [(A.Name, Maybe BindingSource)] <- forM ss $ \s -> do

    let cname = C.QName $ C.Name r C.InScope $ C.stringNameParts s
    -- Note: the range in the concrete name is only approximate.
    -- Jesper, 2018-12-19: Don't consider generalizable names since
    -- they can be shadowed by hidden variables.
    resolveName' (exceptKindsOfNames [GeneralizeName]) Nothing cname >>= \case

      -- Fail if s is a name, but not of a variable.
      DefinedName{}       -> failNotVar s
      FieldName{}         -> failNotVar s
      ConstructorName{}   -> failNotVar s
      PatternSynResName{} -> failNotVar s

      -- If s is a variable name, return it together with binding information.
      VarName x b -> return (x, Just b)

      -- If s is not a name, compare it to the printed variable representation.
      UnknownName -> case (lookup s xs) of
        Nothing -> failUnbound s
        Just x  -> return (x, Nothing)

  -- Step 2: Resolve each abstract name to a de Bruijn index.

  -- First, get context names of the clause.
  let clauseCxtNames = map (fst . unDom) cxt

  -- Valid names to split on are pattern variables of the clause,
  -- plus as-bindings that refer to a variable.
  let clauseVars = zip clauseCxtNames (map var [0..]) ++
                   map (\(AsB name v _ _) -> (name,v)) asb

  -- We cannot split on module parameters or make them visible
  params <- moduleParamsToApply $ qnameModule f
  let isParam i = any ((== var i) . unArg) params

  forM (zip ss abstractNames) $ \(s, (name, bound)) -> case bound of
    -- Case 1: variable has a binding site. Check if it also exists in
    -- the clause context so we can split on it.
    Just bindingSource -> case (lookup name clauseVars, bindingSource) of
      -- Case 1a: it is also known in the clause telescope and is
      -- actually a variable. If a pattern variable (`PatternBound`)
      -- has been refined to a module parameter we do allow splitting
      -- on it, since the instantiation could as well have been the
      -- other way around (see #2183).
      (Just (Var i []), PatternBound) -> return (i, C.InScope)
      -- Case 1b: the variable has been refined.
      (Just v         , PatternBound) -> failInstantiatedVar s v
      -- Case 1c: the variable is bound locally (e.g. a record let)
      (Nothing        , PatternBound) -> failCaseLet s
      -- Case 1d: module parameter
      (Just (Var i []), LambdaBound ) -> failModuleBound s
      -- Case 1e: locally lambda-bound variable
      (_              , LambdaBound ) -> failLocal s
      -- Case 1f: let-bound variable
      (_              , LetBound    ) -> failLetBound s
      -- Case 1g: with-bound variable (not used?)
      (_              , WithBound   ) -> __IMPOSSIBLE__
    -- Case 2: variable has no binding site, so we check if it can be
    -- made visible.
    Nothing -> case List.find (((==) `on` nameConcrete) name . fst) clauseVars of
      -- Case 2a: there is a variable with that concrete name in the
      -- clause context. If it is not a parameter, we can make it
      -- visible.
      Just (x, Var i []) | isParam i -> failHiddenModuleBound s
                         | otherwise -> return (i, C.NotInScope)
      -- Case 2b: there is a variable with that concrete name, but it
      -- has been refined.
      Just (x, v) -> failInstantiatedVar s v
      -- Case 2c: there is no variable with that name. Since it was in
      -- scope for the interaction meta, the only possibility is that
      -- it is a hidden lambda-bound variable.
      Nothing -> failHiddenLocal s

  where

  failNotVar s      = typeError $ GenericError $ "Not a variable: " ++ s
  failUnbound s     = typeError $ GenericError $ "Unbound variable " ++ s
  failAmbiguous s   = typeError $ GenericError $ "Ambiguous variable " ++ s
  failLocal s       = typeError $ GenericError $
    "Cannot split on local variable " ++ s
  failHiddenLocal s = typeError $ GenericError $
    "Cannot make hidden lambda-bound variable " ++ s ++ " visible"
  failModuleBound s = typeError $ GenericError $
    "Cannot split on module parameter " ++ s
  failHiddenModuleBound s = typeError $ GenericError $
    "Cannot make hidden module parameter " ++ s ++ " visible"
  failLetBound s = typeError . GenericError $
    "Cannot split on let-bound variable " ++ s
  failInstantiatedVar s v = typeError . GenericDocError =<< sep
      [ text $ "Cannot split on variable " ++ s ++ ", because it is bound to"
      , prettyTCM v
      ]
  failCaseLet s     = typeError $ GenericError $
    "Cannot split on variable " ++ s ++
    ", because let-declarations may not be defined by pattern-matching"



-- | Lookup the clause for an interaction point in the signature.
--   Returns the CaseContext, the previous clauses, the clause itself,
--   and a list of the remaining ones.

type ClauseZipper =
   ( [Clause] -- previous clauses
   , Clause   -- clause of interest
   , [Clause] -- other clauses
   )

getClauseZipperForIP :: QName -> Int -> TCM (CaseContext, ClauseZipper)
getClauseZipperForIP f clauseNo = do
  (theDef <$> getConstInfo f) >>= \case
    Function{funClauses = cs, funExtLam = extlam} -> do
      let (cs1,ccs2) = fromMaybe __IMPOSSIBLE__ $ splitExactlyAt clauseNo cs
          (c,cs2)    = fromMaybe __IMPOSSIBLE__ $ uncons ccs2
      return (extlam, (cs1, c, cs2))
    d -> do
      reportSDoc "impossible" 10 $ vcat
        [ "getClauseZipperForIP" <+> prettyTCM f <+> text (show clauseNo)
          <+> "received"
        , text (show d)
        ]
      __IMPOSSIBLE__

recheckAbstractClause :: Type -> Maybe Substitution -> A.SpineClause -> TCM (Clause, Context, [AsBinding])
recheckAbstractClause t sub acl = checkClauseLHS t sub acl $ \ lhs -> do
  let cl = Clause { clauseLHSRange    = getRange acl
                  , clauseFullRange   = getRange acl
                  , clauseTel         = lhsVarTele lhs
                  , namedClausePats   = lhsPatterns lhs
                  , clauseBody        = Nothing -- We don't need the body for make case
                  , clauseType        = Just (lhsBodyType lhs)
                  , clauseCatchall    = False
                  , clauseExact       = Nothing
                  , clauseRecursive   = Nothing
                  , clauseUnreachable = Nothing
                  , clauseEllipsis    = lhsEllipsis $ A.spLhsInfo $ A.clauseLHS acl
                  , clauseWhereModule = A.whereModule $ A.clauseWhereDecls acl
                  }
  cxt <- getContext
  let asb = lhsAsBindings lhs
  return (cl, cxt, asb)


-- | Entry point for case splitting tactic.

makeCase :: InteractionId -> Range -> String -> TCM (QName, CaseContext, [A.Clause])
makeCase hole rng s = withInteractionId hole $ locallyTC eMakeCase (const True) $ do

  -- Jesper, 2018-12-10: print unsolved metas in dot patterns as _
  localTC (\ e -> e { envPrintMetasBare = True }) $ do

  -- Get function clause which contains the interaction point.
  InteractionPoint { ipMeta = mm, ipClause = ipCl} <- lookupInteractionPoint hole
  (f, clauseNo, clTy, clWithSub, absCl@A.Clause{ clauseRHS = rhs }, clClos) <- case ipCl of
    IPClause f i t sub cl clo -> return (f, i, t, sub, cl, clo)
    IPNoClause                -> typeError $ GenericError $
      "Cannot split here, as we are not in a function definition"
  (casectxt, (prevClauses0, _clause, follClauses0)) <- getClauseZipperForIP f clauseNo

  -- Instead of using the actual internal clause, we retype check the abstract clause (with
  -- eMakeCase = True). This disables the forcing translation in the unifier, which allows us to
  -- split on forced variables.
  (clause, clauseCxt, clauseAsBindings) <-
    enterClosure clClos $ \ _ -> locallyTC eMakeCase (const True) $
      recheckAbstractClause clTy clWithSub absCl

  let (prevClauses, follClauses) = killRange (prevClauses0, follClauses0)
    -- Andreas, 2019-08-08, issue #3966
    -- Kill the ranges of the existing clauses to prevent wrong error
    -- location to be set by the coverage checker (via isCovered)
    -- for test/interaction/Issue191
  let perm = fromMaybe __IMPOSSIBLE__ $ clausePerm clause
      tel  = clauseTel  clause
      ps   = namedClausePats clause
      ell  = clauseEllipsis clause
  reportSDoc "interaction.case" 100 $ vcat
    [ "splitting clause:"
    , nest 2 $ vcat
      [ "f       =" <+> (text . show) f
      , "context =" <+> ((inTopContext . (text . show)) =<< getContextTelescope)
      , "tel     =" <+> (text . show) tel
      , "perm    =" <+> text (show perm)
      , "ps      =" <+> (text . show) ps
      ]
    ]
  reportSDoc "interaction.case" 60 $ vcat
    [ "splitting clause:"
    , nest 2 $ vcat
      [ "f       =" <+> pretty f
      , "context =" <+> ((inTopContext . pretty) =<< getContextTelescope)
      , "tel     =" <+> pretty tel
      , "perm    =" <+> (text . show) perm
      , "ps      =" <+> pretty ps
      ]
    ]
  reportSDoc "interaction.case" 10 $ vcat
    [ "splitting clause:"
    , nest 2 $ vcat
      [ "f       =" <+> prettyTCM f
      , "context =" <+> ((inTopContext . prettyTCM) =<< getContextTelescope)
      , "tel     =" <+> (inTopContext . prettyTCM) tel
      , "perm    =" <+> text (show perm)
      , "ps      =" <+> addContext tel (prettyTCMPatternList ps)
      , "ell     =" <+> text (show ell)
      , "type    =" <+> addContext tel (prettyTCM $ clauseType clause)
      ]
    ]

  -- Check split variables.

  let vars = words s

  -- If the user just entered ".", do nothing.
  -- This will expand an ellipsis, if present.

  if concat vars == "." then do
    cl <- makeAbstractClause f rhs NoEllipsis $ clauseToSplitClause clause
    return (f, casectxt, [cl])

  -- If we have no split variables, split on result.

  else if null vars then do
    -- Andreas, 2017-07-24, issue #2654:
    -- When we introduce projection patterns in an extended lambda,
    -- we need to print them postfix.
    let postProjInExtLam = applyWhen (isJust casectxt) $
          withPragmaOptions $ \ opt -> opt { optPostfixProjections = True }
    (piTel, sc) <- insertTrailingArgs False $ clauseToSplitClause clause
    -- Andreas, 2015-05-05 If we introduced new function arguments
    -- do not split on result.  This might be more what the user wants.
    -- To split on result, he can then C-c C-c again.
    -- Andreas, 2015-05-21 Issue 1516:  However, if only hidden
    -- arguments are introduced, C-c C-c virtually does nothing
    -- (as they are not shown and get lost on the way to emacs and back).
    newPats <- if null piTel then return False else do
      -- If there were any pattern introduce, they will only have effect
      -- if any of them is shown by the printer
      imp <- optShowImplicit <$> pragmaOptions
      return $ imp || any visible (telToList piTel)
    scs <- if newPats then return [sc] else postProjInExtLam $ do
      res <- splitResult f sc
      case res of

        Left err  -> do
          -- Andreas, 2017-12-16, issue #2871
          -- If there is nothing to split, introduce trailing hidden arguments.

          -- Get trailing hidden pattern variables
          let trailingPatVars :: [NamedArg DBPatVar]
              trailingPatVars = takeWhileJust isVarP $ reverse ps
              isVarP (Arg ai (Named n (VarP _ x))) = Just $ Arg ai $ Named n x
              isVarP _ = Nothing
          -- If all are already coming from the user, there is really nothing todo!
          when (all ((UserWritten ==) . getOrigin) trailingPatVars) $ do
            typeError $ SplitError err
          -- Otherwise, we make these user-written
          let xs = map (dbPatVarIndex . namedArg) trailingPatVars
          return [makePatternVarsVisible xs sc]

        Right cov -> ifNotM (optCopatterns <$> pragmaOptions) failNoCop $ {-else-} do
          -- Andreas, 2016-05-03: do not introduce function arguments after projection.
          -- This is sometimes annoying and can anyway be done by another C-c C-c.
          -- mapM (snd <.> fixTarget) $ splitClauses cov
          return cov
    checkClauseIsClean ipCl
    (f, casectxt,) <$> do
      -- Andreas, 2020-05-18, issue #4536
      -- When result splitting yields no clauses, replace rhs by @record{}@.
      if null scs then
        return [ A.spineToLhs $ absCl{ A.clauseRHS = makeRHSEmptyRecord rhs } ]
      else mapM (makeAbstractClause f rhs ell) scs
  else do
    -- split on variables
    xs <- parseVariables f clauseCxt clauseAsBindings hole rng vars
    reportSLn "interaction.case" 30 $ "parsedVariables: " ++ show (zip xs vars)
    -- Variables that are not in scope yet are brought into scope (@toShow@)
    -- The other variables are split on (@toSplit@).
    let (toShow, toSplit) = partitionEithers $ for (zip xs vars) $ \ ((x,nis), s) ->
          if (nis == C.NotInScope) then Left x else Right x
    let sc = makePatternVarsVisible toShow $ clauseToSplitClause clause
    scs <- split f toSplit sc
    reportSLn "interaction.case" 70 $ "makeCase: survived the splitting"

    -- If any of the split variables is hidden by the ellipsis, we
    -- should force the expansion of the ellipsis.
    let splitNames = map (\i -> fst $ unDom $ clauseCxt !! i) toSplit
    shouldExpandEllipsis <- return (not $ null toShow) `or2M` anyEllipsisVar f absCl splitNames
    let ell' | shouldExpandEllipsis = NoEllipsis
             | otherwise            = ell

    -- CLEAN UP OF THE GENERATED CLAUSES
    -- 1. filter out the generated clauses that are already covered
    --    we consider a generated clause already covered if it is covered by:
    --    a. a pre-existing clause defined before the one we splitted (prevClauses)
    --    b. a pre-existing clause defined after the one we splitted (follClauses)
    --       under the condition that it did not cover the one we splitted but was
    --       covered by it (i.e. it was considered unreachable).
    -- The key idea here is:
    --       f m    zero = ?  ---- split on m --->  f (suc m) zero = ?
    --       f zero zero = ?                        f zero    zero = ?
    --       f _    _    = ?                        f _       _    = ?
    -- because [f zero zero] is already defined.
    -- However we ignore [f _ _]: [f m zero] was already a refinement of it,
    -- hinting that we considered it more important than the catchall.
    let sclause = clauseToSplitClause clause
    fcs <- filterM (\ cl -> (isCovered f [clause] (clauseToSplitClause cl)) `and2M`
                            (not <$> isCovered f [cl] sclause))
                   follClauses
    scs <- filterM (not <.> isCovered f (prevClauses ++ fcs) . fst) scs
    reportSLn "interaction.case" 70 $ "makeCase: survived filtering out already covered clauses"
    -- 2. filter out trivially impossible clauses not asked for by the user
    cs <- catMaybes <$> do
     forM scs $ \ (sc, isAbsurd) -> if isAbsurd
      -- absurd clause coming from a split asked for by the user
      then Just <$> makeAbsurdClause f ell' sc
      -- trivially empty clause due to the refined patterns
      else
        ifM (liftTCM $ (optInferAbsurdClauses <$> pragmaOptions) `and2M` isEmptyTel (scTel sc))
          {- then -} (pure Nothing)
          {- else -} (Just <$> makeAbstractClause f rhs ell' sc)
    reportSLn "interaction.case" 70 $ "makeCase: survived filtering out impossible clauses"
    -- 3. If the cleanup removed everything then we know that none of the clauses where
    --    absurd but that all of them were trivially empty. In this case we rewind and
    --    insert all the clauses (garbage in, garbage out!)
    cs <- if not (null cs) then pure cs
          else mapM (makeAbstractClause f rhs ell' . fst) scs

    reportSDoc "interaction.case" 65 $ vcat
      [ "split result:"
      , nest 2 $ vcat $ map prettyA cs
      ]
    checkClauseIsClean ipCl
    return (f, casectxt, cs)

  where
  failNoCop = typeError $ GenericError $
    "OPTION --copatterns needed to split on result here"

  -- Split clause on given variables, return the resulting clauses together
  -- with a bool indicating whether each clause is absurd
  split :: QName -> [Nat] -> SplitClause -> TCM [(SplitClause, Bool)]
  split f [] clause = return [(clause,False)]
  split f (var : vars) clause = do
    z <- dontAssignMetas $ splitClauseWithAbsurd clause var
    case z of
      Left err          -> typeError $ SplitError err
      Right (Left cl)   -> return [(cl,True)]
      Right (Right cov) -> concat <$> do
            forM (splitClauses cov) $ \ cl ->
              split f (mapMaybe (newVar cl) vars) cl

  -- Finds the new variable corresponding to an old one, if any.
  newVar :: SplitClause -> Nat -> Maybe Nat
  newVar c x = case applySplitPSubst (scSubst c) (var x) of
    Var y [] -> Just y
    _        -> Nothing

  -- Check whether clause has been refined after last load.
  -- In this case, we refuse to split, as this might lose the refinements.
  checkClauseIsClean :: IPClause -> TCM ()
  checkClauseIsClean ipCl = do
    sips <- filter ipSolved . BiMap.elems <$> useTC stInteractionPoints
    when (List.any ((== ipCl) . ipClause) sips) $
      typeError $ GenericError $ "Cannot split as clause rhs has been refined.  Please reload"

-- | Make the given pattern variables visible by marking their origin as
--   'CaseSplit' and pattern origin as 'PatOSplit' in the 'SplitClause'.
makePatternVarsVisible :: [Nat] -> SplitClause -> SplitClause
makePatternVarsVisible [] sc = sc
makePatternVarsVisible is sc@SClause{ scPats = ps } =
  sc{ scPats = mapNamedArgPattern mkVis ps }
  where
  mkVis :: NamedArg SplitPattern -> NamedArg SplitPattern
  mkVis (Arg ai (Named n (VarP o (SplitPatVar x i ls))))
    | i `elem` is =
      -- We could introduce extra consistency checks, like
      -- if visible ai then __IMPOSSIBLE__ else
      -- or passing the parsed name along and comparing it with @x@
      Arg (setOrigin CaseSplit ai) $ Named n $ VarP (PatternInfo PatOSplit []) $ SplitPatVar x i ls
  mkVis np = np

-- | If a copattern split yields no clauses, we must be at an empty record type.
--   In this case, replace the rhs by @record{}@
makeRHSEmptyRecord :: A.RHS -> A.RHS
makeRHSEmptyRecord = \case
  A.RHS{}            -> A.RHS{ rhsExpr = A.Rec empty empty, rhsConcrete = Nothing }
  rhs@A.RewriteRHS{} -> rhs{ A.rewriteRHS = makeRHSEmptyRecord $ A.rewriteRHS rhs }
  A.AbsurdRHS        -> __IMPOSSIBLE__
  A.WithRHS{}        -> __IMPOSSIBLE__

-- | Make clause with no rhs (because of absurd match).

makeAbsurdClause :: QName -> ExpandedEllipsis -> SplitClause -> TCM A.Clause
makeAbsurdClause f ell (SClause tel sps _ _ t) = do
  let ps = fromSplitPatterns sps
  reportSDoc "interaction.case" 10 $ vcat
    [ "Interaction.MakeCase.makeAbsurdClause: split clause:"
    , nest 2 $ vcat
      [ "context =" <+> do (inTopContext . prettyTCM) =<< getContextTelescope
      , "tel     =" <+> do inTopContext $ prettyTCM tel
      , "ps      =" <+> do inTopContext $ addContext tel $ prettyTCMPatternList ps -- P.sep <$> prettyTCMPatterns ps
      , "ell     =" <+> text (show ell)
      ]
    ]
  withCurrentModule (qnameModule f) $
    -- Andreas, 2015-05-29 Issue 635
    -- Contract implicit record patterns before printing.
    -- c <- translateRecordPatterns $ Clause noRange tel perm ps NoBody t False
    -- Jesper, 2015-09-19 Don't contract, since we do on-demand splitting
    inTopContext $ reify $ QNamed f $ Clause
      { clauseLHSRange  = noRange
      , clauseFullRange = noRange
      , clauseTel       = tel
      , namedClausePats = ps
      , clauseBody      = Nothing
      , clauseType      = argFromDom <$> t
      , clauseCatchall    = False
      , clauseExact       = Nothing
      , clauseRecursive   = Nothing
      , clauseUnreachable = Nothing
      , clauseEllipsis    = ell
      , clauseWhereModule = Nothing
      }

-- | Make a clause with a question mark as rhs.

makeAbstractClause :: QName -> A.RHS -> ExpandedEllipsis -> SplitClause -> TCM A.Clause
makeAbstractClause f rhs ell cl = do

  lhs <- A.clauseLHS <$> makeAbsurdClause f ell cl
  reportSDoc "interaction.case" 60 $ "reified lhs: " <+> prettyA lhs
  return $ A.Clause lhs [] rhs A.noWhereDecls False
  -- let ii = InteractionId (-1)  -- Dummy interaction point since we never type check this.
  --                              -- Can end up in verbose output though (#1842), hence not __IMPOSSIBLE__.
  -- let info = A.emptyMetaInfo   -- metaNumber = Nothing in order to print as ?, not ?n
  -- return $ A.Clause lhs [] (A.RHS $ A.QuestionMark info ii) [] False

anyEllipsisVar :: QName -> A.SpineClause -> [Name] -> TCM Bool
anyEllipsisVar f cl xs = do
  let lhs = A.clauseLHS cl
      ps  = A.spLhsPats lhs
      ell = lhsEllipsis $ A.spLhsInfo lhs
      anyVar :: A.Pattern -> Any -> Any
      anyVar p acc = Any $ getAny acc || case p of
        A.VarP x -> A.unBind x `elem` xs
        _        -> False
  case ell of
    NoEllipsis           -> return False
    ExpandedEllipsis _ k -> do
      ps' <- snd <$> reifyDisplayFormP f ps []
      let ellipsisPats :: A.Patterns
          ellipsisPats = fst $ C.splitEllipsis k ps'
      reportSDoc "interaction.case.ellipsis" 40 $ vcat
        [ "should we expand the ellipsis?"
        , nest 2 $ "xs           =" <+> prettyList_ (map prettyA xs)
        , nest 2 $ "ellipsisPats =" <+> prettyList_ (map prettyA ellipsisPats)
        ]
      return $ getAny $ A.foldrAPattern anyVar ellipsisPats
