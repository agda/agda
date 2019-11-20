{-# LANGUAGE NondecreasingIndentation #-}
{-# LANGUAGE GADTs                     #-}

module Agda.Interaction.MakeCase where

import Prelude hiding (mapM, mapM_, null)

import Control.Monad hiding (mapM, mapM_, forM)

import Data.Either
import Data.Foldable (traverse_)
import qualified Data.Map as Map
import qualified Data.List as List
import Data.Maybe
import Data.Traversable (mapM, forM)

import Agda.Syntax.Common
import Agda.Syntax.Position
import Agda.Syntax.Concrete (NameInScope(..))
import qualified Agda.Syntax.Concrete as C
import qualified Agda.Syntax.Abstract as A
import Agda.Syntax.Internal
import Agda.Syntax.Internal.Pattern
import Agda.Syntax.Scope.Base  ( ResolvedName(..), BindingSource(..), KindOfName(..), exceptKindsOfNames, inverseScopeLookupName', AllowAmbiguousNames(..) )
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
import Agda.TypeChecking.Rules.Term (isModuleFreeVar)

import Agda.Interaction.Options
import Agda.Interaction.BasicOps

import Agda.Utils.Function
import Agda.Utils.Functor
import Agda.Utils.List
import Agda.Utils.Monad
import Agda.Utils.Null
import qualified Agda.Utils.Pretty as P
import Agda.Utils.Size

import Agda.Utils.Impossible

type CaseContext = Maybe ExtLamInfo

-- | Parse variables (visible or hidden), returning their de Bruijn indices.
--   Used in 'makeCase'.

parseVariables
  :: QName           -- ^ The function name.
  -> Telescope       -- ^ The telescope of the clause we are splitting.
  -> InteractionId   -- ^ The hole of this function we are working on.
  -> Range           -- ^ The range of this hole.
  -> [String]        -- ^ The words the user entered in this hole (variable names).
  -> TCM [(Int,NameInScope)] -- ^ The computed de Bruijn indices of the variables to split on,
                             --   with information about whether each variable is in scope.
parseVariables f tel ii rng ss = do

  -- Get into the context of the meta.
  mId <- lookupInteractionId ii
  updateMetaVarRange mId rng
  mi  <- getMetaInfo <$> lookupMeta mId
  enterClosure mi $ \ r -> do

    -- Get printed representation of variables in context.
    n  <- getContextSize
    xs <- forM (downFrom n) $ \ i -> do
      (,i) . P.render <$> prettyTCM (var i)

    -- We might be under some lambdas, in which case the context
    -- is bigger than the number of pattern variables.
    let nPatVars = size tel
    let nlocals = n - nPatVars
    unless (nlocals >= 0) __IMPOSSIBLE__  -- cannot be negative

    fv <- getDefFreeVars f
    reportSDoc "interaction.case" 20 $ do
      m   <- currentModule
      tel <- lookupSection m
      cxt <- getContextTelescope
      vcat
       [ "parseVariables:"
       , "current module  =" <+> prettyTCM m
       , "current section =" <+> inTopContext (prettyTCM tel)
       , text $ "function's fvs  = " ++ show fv
       , text $ "number of locals= " ++ show nlocals
       , "context         =" <+> do inTopContext $ prettyTCM cxt
       , "checkpoints     =" <+> do (text . show) =<< asksTC envCheckpoints
       ]

    -- Resolve each string to a variable.
    forM ss $ \ s -> do
      let failNotVar      = typeError $ GenericError $ "Not a variable: " ++ s
          failUnbound     = typeError $ GenericError $ "Unbound variable " ++ s
          failAmbiguous   = typeError $ GenericError $ "Ambiguous variable " ++ s
          failLocal       = typeError $ GenericError $
            "Cannot split on local variable " ++ s
          failModuleBound = typeError $ GenericError $
            "Cannot split on module parameter " ++ s
          failLetBound v  = typeError . GenericError $
            "Cannot split on let-bound variable " ++ s
          failInstantiatedVar v = typeError . GenericDocError =<< sep
              [ text $ "Cannot split on variable " ++ s ++ ", because it is bound to"
              , prettyTCM v
              ]
          failCaseLet     = typeError $ GenericError $
            "Cannot split on variable " ++ s ++
            ", because let-declarations may not be defined by pattern-matching"

      let cname = C.QName $ C.Name r C.InScope $ C.stringNameParts s
      -- Note: the range in the concrete name is only approximate.
      -- Jesper, 2018-12-19: Don't consider generalizable names since
      -- they can be shadowed by hidden variables.
      resolveName' (exceptKindsOfNames [GeneralizeName]) Nothing cname >>= \case

        -- Fail if s is a name, but not of a variable.
        DefinedName{}       -> failNotVar
        FieldName{}         -> failNotVar
        ConstructorName{}   -> failNotVar
        PatternSynResName{} -> failNotVar

        -- If s is a variable name in scope, get its de Bruijn index
        -- via the type checker.
        VarName x b -> do
          (v, _) <- getVarInfo x
          case (v , b) of
            -- Slightly dangerous: the pattern variable `x` may be
            -- refined to the module parameter `var i`. But in this
            -- case the instantiation could as well be the other way
            -- around, so the new clauses will still make sense.
            (Var i [] , PatternBound) -> do
              reportSLn "interaction.case" 30 $ "resolved variable " ++ show x ++ " = " ++ show i
              when (i < nlocals) failCaseLet
              return (i - nlocals , C.InScope)
            (Var i [] , LambdaBound)
              | i < nlocals -> failLocal
              | otherwise   -> failModuleBound
            (Var i [] , LetBound) -> failLetBound v
            (_        , _       ) -> failInstantiatedVar v

        -- If s is not a name, compare it to the printed variable representation.
        -- This fallback is to enable splitting on hidden variables.
        UnknownName -> do
          let xs' = filter ((s ==) . fst) xs
          when (null xs') $ failUnbound
          reportSLn "interaction.case" 20 $ "matching names corresponding to indices " ++ show xs'
          -- Andreas, 2018-05-28, issue #3095
          -- We want to act on an ambiguous name if it corresponds to only one local index.
          let xs'' = mapMaybe (\ (_,i) -> if i < nlocals then Nothing else Just $ i - nlocals) xs'
          when (null xs'') $ typeError $ GenericError $
            "Cannot make hidden lambda-bound variable " ++ s ++ " visible"
          -- Filter out variable bound by parent function or module.
          params <- moduleParamsToApply $ qnameModule f
          let isParam i = any ((== var i) . unArg) params
              xs'''     = filter (not . isParam) xs''
          when (null xs''') $ typeError $ GenericError $
            "Cannot make hidden module parameter " ++ s ++ " visible"
          case xs''' of
            []  -> failModuleBound
            [i] -> return (i , C.NotInScope)
            -- Issue 1325: Variable names in context can be ambiguous.
            _   -> failAmbiguous

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

recheckAbstractClause :: Type -> Maybe Substitution -> A.SpineClause -> TCM Clause
recheckAbstractClause t sub cl = checkClauseLHS t sub cl $ \ lhs ->
  return Clause{ clauseLHSRange    = getRange cl
               , clauseFullRange   = getRange cl
               , clauseTel         = lhsVarTele lhs
               , namedClausePats   = lhsPatterns lhs
               , clauseBody        = Nothing -- We don't need the body for make case
               , clauseType        = Just (lhsBodyType lhs)
               , clauseCatchall    = False
               , clauseUnreachable = Nothing }

-- | Entry point for case splitting tactic.

makeCase :: InteractionId -> Range -> String -> TCM (QName, CaseContext, [A.Clause])
makeCase hole rng s = withInteractionId hole $ locallyTC eMakeCase (const True) $ do

  -- Jesper, 2018-12-10: print unsolved metas in dot patterns as _
  localTC (\ e -> e { envPrintMetasBare = True }) $ do

  -- Get function clause which contains the interaction point.
  InteractionPoint { ipMeta = mm, ipClause = ipCl} <- lookupInteractionPoint hole
  let meta = fromMaybe __IMPOSSIBLE__ mm
  (f, clauseNo, clTy, clWithSub, absCl@A.Clause{ clauseRHS = rhs }, clClos) <- case ipCl of
    IPClause f i t sub cl clo _ -> return (f, i, t, sub, cl, clo)
    IPNoClause                -> typeError $ GenericError $
      "Cannot split here, as we are not in a function definition"
  (casectxt, (prevClauses0, _clause, follClauses0)) <- getClauseZipperForIP f clauseNo

  -- Instead of using the actual internal clause, we retype check the abstract clause (with
  -- eMakeCase = True). This disables the forcing translation in the unifier, which allows us to
  -- split on forced variables.
  clause <- enterClosure clClos $ \ _ -> locallyTC eMakeCase (const True) $
              recheckAbstractClause clTy clWithSub absCl

  let (prevClauses, follClauses) = killRange (prevClauses0, follClauses0)
    -- Andreas, 2019-08-08, issue #3966
    -- Kill the ranges of the existing clauses to prevent wrong error
    -- location to be set by the coverage checker (via isCovered)
    -- for test/interaction/Issue191
  let perm = fromMaybe __IMPOSSIBLE__ $ clausePerm clause
      tel  = clauseTel  clause
      ps   = namedClausePats clause
  reportSDoc "interaction.case" 10 $ vcat
    [ "splitting clause:"
    , nest 2 $ vcat
      [ "f       =" <+> prettyTCM f
      , "context =" <+> ((inTopContext . prettyTCM) =<< getContextTelescope)
      , "tel     =" <+> (inTopContext . prettyTCM) tel
      , "perm    =" <+> text (show perm)
      , "ps      =" <+> prettyTCMPatternList ps
      ]
    ]
  reportSDoc "interaction.case" 60 $ vcat
    [ "splitting clause:"
    , nest 2 $ vcat
      [ "f       =" <+> (text . show) f
      , "context =" <+> ((inTopContext . (text . show)) =<< getContextTelescope)
      , "tel     =" <+> (text . show) tel
      , "perm    =" <+> text (show perm)
      , "ps      =" <+> (text . show) ps
      ]
    ]

  -- Check split variables.

  let vars = words s

  -- If the user just entered ".", do nothing.
  -- This will expand an ellipsis, if present.

  if concat vars == "." then do
    cl <- makeAbstractClause f rhs $ clauseToSplitClause clause
    return (f, casectxt, [cl])

  -- If we have no split variables, split on result.

  else if null vars then do
    -- Andreas, 2017-07-24, issue #2654:
    -- When we introduce projection patterns in an extended lambda,
    -- we need to print them postfix.
    let postProjInExtLam = applyWhen (isJust casectxt) $
          withPragmaOptions $ \ opt -> opt { optPostfixProjections = True }
    (piTel, sc) <- insertTrailingArgs $ clauseToSplitClause clause
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
    (f, casectxt,) <$> mapM (makeAbstractClause f rhs) scs
  else do
    -- split on variables
    xs <- parseVariables f tel hole rng vars
    reportSLn "interaction.case" 30 $ "parsedVariables: " ++ show (zip xs vars)
    -- Variables that are not in scope yet are brought into scope (@toShow@)
    -- The other variables are split on (@toSplit@).
    let (toShow, toSplit) = partitionEithers $ for (zip xs vars) $ \ ((x,nis), s) ->
          if (nis == C.NotInScope) then Left x else Right x
    let sc = makePatternVarsVisible toShow $ clauseToSplitClause clause
    scs <- split f toSplit sc
    reportSLn "interaction.case" 70 $ "makeCase: survived the splitting"

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
      then Just <$> makeAbsurdClause f sc
      -- trivially empty clause due to the refined patterns
      else
        ifM (liftTCM $ isEmptyTel (scTel sc))
          {- then -} (pure Nothing)
          {- else -} (Just <$> makeAbstractClause f rhs sc)
    reportSLn "interaction.case" 70 $ "makeCase: survived filtering out impossible clauses"
    -- 3. If the cleanup removed everything then we know that none of the clauses where
    --    absurd but that all of them were trivially empty. In this case we rewind and
    --    insert all the clauses (garbage in, garbage out!)
    cs <- if not (null cs) then pure cs
          else mapM (makeAbstractClause f rhs . fst) scs

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
    sips <- filter ipSolved . Map.elems <$> useTC stInteractionPoints
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

-- | Make clause with no rhs (because of absurd match).

makeAbsurdClause :: QName -> SplitClause -> TCM A.Clause
makeAbsurdClause f (SClause tel sps _ _ t) = do
  let ps = fromSplitPatterns sps
  reportSDoc "interaction.case" 10 $ vcat
    [ "Interaction.MakeCase.makeAbsurdClause: split clause:"
    , nest 2 $ vcat
      [ "context =" <+> do (inTopContext . prettyTCM) =<< getContextTelescope
      , "tel     =" <+> do inTopContext $ prettyTCM tel
      , "ps      =" <+> do inTopContext $ addContext tel $ prettyTCMPatternList ps -- P.sep <$> prettyTCMPatterns ps
      ]
    ]
  withCurrentModule (qnameModule f) $ do
    -- Andreas, 2015-05-29 Issue 635
    -- Contract implicit record patterns before printing.
    -- c <- translateRecordPatterns $ Clause noRange tel perm ps NoBody t False
    -- Jesper, 2015-09-19 Don't contract, since we do on-demand splitting
    let c = Clause noRange noRange tel ps Nothing t False Nothing
    -- Normalise the dot patterns
    ps <- addContext tel $ normalise $ namedClausePats c
    reportSDoc "interaction.case" 60 $ "normalized patterns: " <+> prettyTCMPatternList ps
    cl <- inTopContext $ reify $ QNamed f $ c { namedClausePats = ps }

    -- Jesper, 2019-11-18, #4037: check that all constructor /
    -- projection names in the new clause are in scope.
    checkNames cl

    return cl


-- | Make a clause with a question mark as rhs.

makeAbstractClause :: QName -> A.RHS -> SplitClause -> TCM A.Clause
makeAbstractClause f rhs cl = do

  lhs <- A.clauseLHS <$> makeAbsurdClause f cl
  reportSDoc "interaction.case" 60 $ "reified lhs: " <+> prettyA lhs

  return $ A.Clause lhs [] rhs A.noWhereDecls False
  -- let ii = InteractionId (-1)  -- Dummy interaction point since we never type check this.
  --                              -- Can end up in verbose output though (#1842), hence not __IMPOSSIBLE__.
  -- let info = A.emptyMetaInfo   -- metaNumber = Nothing in order to print as ?, not ?n
  -- return $ A.Clause lhs [] (A.RHS $ A.QuestionMark info ii) [] False

-- | Check that all names in the abstract thing are in scope.
class CheckNamesInScope a where
  checkNames :: a -> TCM ()
  default checkNames :: (Foldable f, CheckNamesInScope a', a ~ f a')
                     => a -> TCM ()
  checkNames = traverse_ checkNames

instance CheckNamesInScope a => CheckNamesInScope [a] where
instance CheckNamesInScope a => CheckNamesInScope (Arg a) where
instance CheckNamesInScope a => CheckNamesInScope (Named x a) where
instance CheckNamesInScope a => CheckNamesInScope (C.FieldAssignment' a) where

instance CheckNamesInScope QName where
  checkNames q = do
    ys <- inverseScopeLookupName' AmbiguousConProjs q <$> getScope
    whenNull ys $ typeError . GenericDocError =<< do
      "Cannot split because" <+> prettyTCM q <+> "is not in scope"

instance CheckNamesInScope AmbiguousQName where
  checkNames = checkNames . headAmbQ

instance CheckNamesInScope A.Clause where
  checkNames = checkNames . A.clauseLHS

instance CheckNamesInScope A.LHS where
  checkNames = checkNames . A.lhsCore

instance CheckNamesInScope A.LHSCore where
  checkNames = \case
    A.LHSHead f ps -> checkNames f *> checkNames ps
    A.LHSProj f p qs -> checkNames f *> checkNames p *> checkNames qs
    A.LHSWith h ps qs -> checkNames h *> checkNames ps *> checkNames qs

instance CheckNamesInScope A.Pattern where
  checkNames = \case
    A.VarP{}             -> ok
    A.ConP _ c ps        -> checkNames c *> checkNames ps
    A.ProjP _ _ f        -> checkNames f
    A.DefP _ f p         -> checkNames f *> checkNames p
    A.WildP{}            -> ok
    A.AsP _ _ p          -> checkNames p
    A.DotP{}             -> ok
    A.AbsurdP{}          -> ok
    A.LitP{}             -> ok
    A.PatternSynP _ c ps -> checkNames c *> checkNames ps
    A.RecP _ ps          -> checkNames ps
    A.EqualP _ eqs       -> ok
    A.WithP _ p          -> checkNames p
    where ok = return ()
