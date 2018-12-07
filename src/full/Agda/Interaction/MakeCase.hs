{-# LANGUAGE CPP             #-}

module Agda.Interaction.MakeCase where

import Prelude hiding (mapM, mapM_, null)

import Control.Applicative hiding (empty)
import Control.Monad hiding (mapM, mapM_, forM)
import Control.Monad.Reader (asks)

import qualified Data.Map as Map
import qualified Data.List as List
import Data.Maybe
import Data.Traversable

import Agda.Syntax.Common
import Agda.Syntax.Position
import Agda.Syntax.Concrete (NameInScope(..), LensInScope(..))
import qualified Agda.Syntax.Concrete as C
import qualified Agda.Syntax.Abstract as A
import qualified Agda.Syntax.Abstract.Views as A
import qualified Agda.Syntax.Info as A
import Agda.Syntax.Internal
import Agda.Syntax.Internal.Pattern
import Agda.Syntax.Scope.Base  ( ResolvedName(..), Binder(..) )
import Agda.Syntax.Scope.Monad ( resolveName )
import Agda.Syntax.Translation.ConcreteToAbstract
import Agda.Syntax.Translation.InternalToAbstract

import Agda.TypeChecking.Monad
import Agda.TypeChecking.Coverage
import Agda.TypeChecking.Coverage.Match ( SplitPatVar(..) , SplitPattern , applySplitPSubst , fromSplitPatterns )
import Agda.TypeChecking.Pretty
import Agda.TypeChecking.RecordPatterns
import Agda.TypeChecking.Reduce
import Agda.TypeChecking.Substitute
import Agda.TypeChecking.Irrelevance
import Agda.TypeChecking.Rules.LHS.Implicit
import Agda.TheTypeChecker

import Agda.Interaction.Options
import Agda.Interaction.BasicOps

import Agda.Utils.Function
import Agda.Utils.Functor
import Agda.Utils.Lens
import Agda.Utils.List
import Agda.Utils.Monad
import Agda.Utils.Null
import qualified Agda.Utils.Pretty as P
import Agda.Utils.Singleton
import Agda.Utils.Size
import qualified Agda.Utils.HashMap as HMap

#include "undefined.h"
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
    let nlocals = n - size tel
    unless (nlocals >= 0) __IMPOSSIBLE__

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
            "cannot split on let-bound variable " ++ s
          failInstantiatedVar v = typeError . GenericDocError =<< sep
              [ text $ "Cannot split on variable " ++ s ++ ", because it is bound to"
              , prettyTCM v
              ]

      -- Note: the range in the concrete name is only approximate.
      resName <- resolveName $ C.QName $ C.Name r C.InScope $ C.stringNameParts s
      case resName of

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
              when (i < nlocals) __IMPOSSIBLE__
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
          when (null xs'') $ failLocal
          -- Filter out variable bound by parent function or module.
          let xs''' = mapMaybe (\ i -> if i < fv then Nothing else Just i) xs''
          case xs''' of
            []  -> failModuleBound
            [i] -> return (i , C.NotInScope)
            -- Issue 1325: Variable names in context can be ambiguous.
            _   -> failAmbiguous

-- | Lookup the clause for an interaction point in the signature.
--   Returns the CaseContext, the clause itself, and a list of previous clauses

-- Andreas, 2016-06-08, issue #289 and #2006.
-- This replace the old findClause hack (shutter with disgust).
getClauseForIP :: QName -> Int -> TCM (CaseContext, Clause, [Clause])
getClauseForIP f clauseNo = do
  (theDef <$> getConstInfo f) >>= \case
    Function{funClauses = cs, funExtLam = extlam} -> do
      let (cs1,cs2) = fromMaybe __IMPOSSIBLE__ $ splitExactlyAt clauseNo cs
          c         = fromMaybe __IMPOSSIBLE__ $ headMaybe cs2
      return (extlam, c, cs1)
    d -> do
      reportSDoc "impossible" 10 $ vcat
        [ "getClauseForIP" <+> prettyTCM f <+> text (show clauseNo)
          <+> "received"
        , text (show d)
        ]
      __IMPOSSIBLE__


-- | Entry point for case splitting tactic.

makeCase :: InteractionId -> Range -> String -> TCM (QName, CaseContext, [A.Clause])
makeCase hole rng s = withInteractionId hole $ do

  -- Get function clause which contains the interaction point.

  InteractionPoint { ipMeta = mm, ipClause = ipCl} <- lookupInteractionPoint hole
  let meta = fromMaybe __IMPOSSIBLE__ mm
  (f, clauseNo, rhs) <- case ipCl of
    IPClause f clauseNo rhs -> return (f, clauseNo, rhs)
    IPNoClause -> typeError $ GenericError $
      "Cannot split here, as we are not in a function definition"
  (casectxt, clause, prevClauses) <- getClauseForIP f clauseNo
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
      , "ps      =" <+> text (show ps)
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
    (piTel, sc) <- fixTarget $ clauseToSplitClause clause
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
    let (toShow, toSplit) = flip mapEither (zip xs vars) $ \ ((x,nis), s) ->
          if (nis == C.NotInScope) then Left x else Right x
    let sc = makePatternVarsVisible toShow $ clauseToSplitClause clause
    scs <- split f toSplit sc
    -- filter out clauses that are already covered
    scs <- filterM (not <.> isCovered f prevClauses . fst) scs
    cs <- forM scs $ \(sc, isAbsurd) -> do
            if isAbsurd then makeAbsurdClause f sc else makeAbstractClause f rhs sc
    reportSDoc "interaction.case" 65 $ vcat
      [ "split result:"
      , nest 2 $ vcat $ map (text . show . A.deepUnscope) cs
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
      Arg (setOrigin CaseSplit ai) $ Named n $ VarP PatOSplit $ SplitPatVar x i ls
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
    reportSDoc "interaction.case" 60 $ "normalized patterns: " <+> text (show ps)
    inTopContext $ reify $ QNamed f $ c { namedClausePats = ps }


-- | Make a clause with a question mark as rhs.

makeAbstractClause :: QName -> A.RHS -> SplitClause -> TCM A.Clause
makeAbstractClause f rhs cl = do

  lhs <- A.clauseLHS <$> makeAbsurdClause f cl
  reportSDoc "interaction.case" 60 $ "reified lhs: " <+> text (show lhs)
  return $ A.Clause lhs [] rhs A.noWhereDecls False
  -- let ii = InteractionId (-1)  -- Dummy interaction point since we never type check this.
  --                              -- Can end up in verbose output though (#1842), hence not __IMPOSSIBLE__.
  -- let info = A.emptyMetaInfo   -- metaNumber = Nothing in order to print as ?, not ?n
  -- return $ A.Clause lhs [] (A.RHS $ A.QuestionMark info ii) [] False
