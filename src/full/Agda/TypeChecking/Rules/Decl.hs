{-# LANGUAGE CPP #-}
{-# LANGUAGE NondecreasingIndentation #-}

module Agda.TypeChecking.Rules.Decl where

import Prelude hiding (null)

import Control.Monad
import Control.Monad.Reader
import Control.Monad.State (modify, gets, get)
import Control.Monad.Writer (tell)

import Data.Either (partitionEithers)
import qualified Data.Foldable as Fold
import qualified Data.List as List
import Data.Maybe
import Data.Map (Map)
import qualified Data.Sequence as Seq
import qualified Data.Set as Set
import Data.Set (Set)

import Agda.Interaction.Options
import Agda.Interaction.Highlighting.Generate

import qualified Agda.Syntax.Abstract as A
import Agda.Syntax.Abstract.Views (deepUnscopeDecl, deepUnscopeDecls)
import Agda.Syntax.Internal
import qualified Agda.Syntax.Reflected as R
import qualified Agda.Syntax.Info as Info
import Agda.Syntax.Position
import Agda.Syntax.Common
import Agda.Syntax.Literal
import Agda.Syntax.Translation.InternalToAbstract
import Agda.Syntax.Translation.ReflectedToAbstract

import Agda.TypeChecking.Monad
import Agda.TypeChecking.Monad.Builtin
import qualified Agda.TypeChecking.Monad.Benchmark as Bench

import Agda.TypeChecking.Constraints
import Agda.TypeChecking.Conversion
import Agda.TypeChecking.Errors
import Agda.TypeChecking.Injectivity
import Agda.TypeChecking.Irrelevance
import Agda.TypeChecking.Positivity
import Agda.TypeChecking.Positivity.Occurrence
import Agda.TypeChecking.Polarity
import Agda.TypeChecking.Pretty
import Agda.TypeChecking.Primitive
import Agda.TypeChecking.ProjectionLike
import Agda.TypeChecking.Quote
import Agda.TypeChecking.Unquote
import Agda.TypeChecking.Records
import Agda.TypeChecking.RecordPatterns
import Agda.TypeChecking.Reduce
import Agda.TypeChecking.Rewriting
import Agda.TypeChecking.SizedTypes.Solve
import Agda.TypeChecking.Substitute
import Agda.TypeChecking.Telescope
import Agda.TypeChecking.Unquote

import Agda.TypeChecking.Rules.Term
import Agda.TypeChecking.Rules.Data    ( checkDataDef )
import Agda.TypeChecking.Rules.Record  ( checkRecDef )
import Agda.TypeChecking.Rules.Def     ( checkFunDef, newSection, useTerPragma )
import Agda.TypeChecking.Rules.Builtin
import Agda.TypeChecking.Rules.Display ( checkDisplayPragma )

import Agda.Termination.TermCheck

import Agda.Utils.Except
import Agda.Utils.Functor
import Agda.Utils.Function
import Agda.Utils.Lens
import Agda.Utils.Maybe
import Agda.Utils.Monad
import Agda.Utils.Null
import Agda.Utils.Pretty (prettyShow)
import Agda.Utils.Size

#include "undefined.h"
import Agda.Utils.Impossible

-- | Cached checkDecl
checkDeclCached :: A.Declaration -> TCM ()
checkDeclCached d@A.ScopedDecl{} = checkDecl d
checkDeclCached d@(A.Section minfo mname tbinds _) = do
  e <- readFromCachedLog
  reportSLn "cache.decl" 10 $ "checkDeclCached: " ++ show (isJust e)
  case e of
    Just (EnterSection minfo' mname' tbinds', _)
      | killRange minfo == killRange minfo' && mname == mname' && tbinds == tbinds' -> do
        return ()
    _ -> do
      cleanCachedLog
  writeToCurrentLog $ EnterSection minfo mname tbinds
  checkDecl d
  e' <- readFromCachedLog
  case e' of
    Just (LeaveSection mname', _) | mname == mname' -> do
      return ()
    _ -> do
      cleanCachedLog
  writeToCurrentLog $ LeaveSection mname

checkDeclCached d = do
    e <- readFromCachedLog

    reportSLn "cache.decl" 10 $ "checkDeclCached: " ++ show (isJust e)

    case e of
      (Just (Decl d',s)) | compareDecl d d' -> do
        restorePostScopeState s
        reportSLn "cache.decl" 50 $ "range: " ++ show (getRange d)
        printSyntaxInfo (getRange d)
      _ -> do
        cleanCachedLog
        checkDeclWrap d
    writeToCurrentLog $ Decl d
 where
   compareDecl A.Section{} A.Section{} = __IMPOSSIBLE__
   compareDecl A.ScopedDecl{} A.ScopedDecl{} = __IMPOSSIBLE__
   compareDecl x y = x == y
   -- changes to CS inside a RecDef or Mutual ought not happen,
   -- but they do happen, so we discard them.
   ignoreChanges m = do
     cs <- gets $ stLoadedFileCache . stPersistentState
     cleanCachedLog
     _ <- m
     modifyPersistentState $ \st -> st{stLoadedFileCache = cs}
   checkDeclWrap d@A.RecDef{} = ignoreChanges $ checkDecl d
   checkDeclWrap d@A.Mutual{} = ignoreChanges $ checkDecl d
   checkDeclWrap d            = checkDecl d

-- | Type check a sequence of declarations.
checkDecls :: [A.Declaration] -> TCM ()
checkDecls ds = do
  reportSLn "tc.decl" 45 $ "Checking " ++ show (length ds) ++ " declarations..."
  mapM_ checkDecl ds
  -- Andreas, 2011-05-30, unfreezing moved to Interaction/Imports
  -- whenM onTopLevel unfreezeMetas

-- | Type check a single declaration.

checkDecl :: A.Declaration -> TCM ()
checkDecl d = setCurrentRange d $ do
    reportSDoc "tc.decl" 10 $ text "checking declaration"
    debugPrintDecl d
    reportSDoc "tc.decl" 90 $ (text . show) (deepUnscopeDecl d)
    reportSDoc "tc.decl" 10 $ prettyA d  -- Might loop, see e.g. Issue 1597

    -- Issue 418 fix: freeze metas before checking an abstract thing
    -- when_ isAbstract freezeMetas -- WAS IN PLACE 2012-2016, but too crude
    -- applyWhen isAbstract withFreezeMetas $ do -- WRONG

    let -- What kind of final checks/computations should be performed
        -- if we're not inside a mutual block?
        none        m = m $>  Nothing           -- skip all checks
        meta        m = m $>  Just (return ())  -- do the usual checks
        mutual i ds m = m <&> Just . uncurry (mutualChecks i d ds)
        impossible  m = m $>  __IMPOSSIBLE__
                        -- We're definitely inside a mutual block.

    finalChecks <- case d of
      A.Axiom{}                -> meta $ checkTypeSignature d
      A.Field{}                -> typeError FieldOutsideRecord
      A.Primitive i x e        -> meta $ checkPrimitive i x e
      A.Mutual i ds            -> mutual i ds $ checkMutual i ds
      A.Section i x tel ds     -> meta $ checkSection i x tel ds
      A.Apply i x modapp ci _adir -> meta $ checkSectionApplication i x modapp ci
      A.Import i x _adir       -> none $ checkImport i x
      A.Pragma i p             -> none $ checkPragma i p
      A.ScopedDecl scope ds    -> none $ setScope scope >> mapM_ checkDeclCached ds
      A.FunDef i x delayed cs  -> impossible $ check x i $ checkFunDef delayed i x cs
      A.DataDef i x ps cs      -> impossible $ check x i $ checkDataDef i x ps cs
      A.RecDef i x ind eta c ps tel cs -> mutual empty [d] $ check x i $ do
                                    checkRecDef i x ind eta c ps tel cs
                                    blockId <- mutualBlockOf x

                                    -- Andreas, 2016-10-01 testing whether
                                    -- envMutualBlock is set correctly.
                                    -- Apparently not.
                                    verboseS "tc.decl.mutual" 70 $ do
                                      current <- asks envMutualBlock
                                      unless (Just blockId == current) $ do
                                        reportSLn "" 0 $ unlines
                                          [ "mutual block id discrepancy for " ++ prettyShow x
                                          , "  current    mut. bl. = " ++ show current
                                          , "  calculated mut. bl. = " ++ show blockId
                                          ]

                                    return (blockId, Set.singleton x)
      A.DataSig i x ps t       -> impossible $ checkSig i x ps t
      A.RecSig i x ps t        -> none $ checkSig i x ps t
                                  -- A record signature is always followed by a
                                  -- record definition. Metas should not be
                                  -- frozen until after the definition has been
                                  -- checked. NOTE: Metas are not frozen
                                  -- immediately after the last field. Perhaps
                                  -- they should be (unless we're in a mutual
                                  -- block).
      A.Open{}                 -> none $ return ()
      A.PatternSynDef{}        -> none $ return ()
                                  -- Open and PatternSynDef are just artifacts
                                  -- from the concrete syntax, retained for
                                  -- highlighting purposes.
      A.UnquoteDecl mi i x e   -> checkUnquoteDecl mi i x e
      A.UnquoteDef i x e       -> impossible $ checkUnquoteDef i x e

    whenNothingM (asks envMutualBlock) $ do

      -- Syntax highlighting.
      highlight_ d

      -- Post-typing checks.
      whenJust finalChecks $ \ theMutualChecks -> do
        reportSLn "tc.decl" 20 $ "Attempting to solve constraints before freezing."
        wakeupConstraints_   -- solve emptiness and instance constraints
        checkingWhere <- asks envCheckingWhere
        solveSizeConstraints $ if checkingWhere then DontDefaultToInfty else DefaultToInfty
        wakeupConstraints_   -- Size solver might have unblocked some constraints
        reportSLn "tc.decl" 20 $ "Freezing all metas."
        _ <- freezeMetas
        theMutualChecks

    where

    -- check record or data type signature
    checkSig i x ps t = checkTypeSignature $
      A.Axiom A.NoFunSig i defaultArgInfo Nothing x
              (A.Pi (Info.ExprRange (fuseRange ps t)) ps t)

    check x i m = Bench.billTo [Bench.Definition x] $ do
      reportSDoc "tc.decl" 5 $ text "Checking" <+> prettyTCM x <> text "."
      reportSLn "tc.decl.abstract" 25 $ show (Info.defAbstract i)
      r <- abstract (Info.defAbstract i) m
      reportSDoc "tc.decl" 5 $ text "Checked" <+> prettyTCM x <> text "."
      return r

    isAbstract = fmap Info.defAbstract (A.getDefInfo d) == Just AbstractDef

    -- Concrete definitions cannot use information about abstract things.
    abstract ConcreteDef = inConcreteMode
    abstract AbstractDef = inAbstractMode

-- Some checks that should be run at the end of a mutual
-- block (or non-mutual record declaration). The set names
-- contains the names defined in the mutual block.
mutualChecks :: Info.MutualInfo -> A.Declaration -> [A.Declaration] -> MutualId -> Set QName -> TCM ()
mutualChecks mi d ds mid names = do
  -- Andreas, 2014-04-11: instantiate metas in definition types
  let nameList = Set.toList names
  mapM_ instantiateDefinitionType nameList
  -- Andreas, 2017-03-23: check positivity before termination.
  -- This allows us to reuse the information about SCCs
  -- to skip termination of non-recursive functions.
  modifyAllowedReductions (List.delete UnconfirmedReductions) $
    checkPositivity_ mi names
  -- Andreas, 2013-02-27: check termination before injectivity,
  -- to avoid making the injectivity checker loop.
  local (\ e -> e { envMutualBlock = Just mid }) $ checkTermination_ d
  revisitRecordPatternTranslation nameList -- Andreas, 2016-11-19 issue #2308
  -- Andreas, 2015-03-26 Issue 1470:
  -- Restricting coinduction to recursive does not solve the
  -- actual problem, and prevents interesting sound applications
  -- of sized types.
  -- checkCoinductiveRecords  ds
  -- Andreas, 2012-09-11:  Injectivity check stores clauses
  -- whose 'Relevance' is affected by polarity computation,
  -- so do it here (again).
  -- Andreas, 2015-07-01:  In particular, 'UnusedArg's of local functions
  -- are only recognized after the polarity computation.
  -- See Issue 1366 for an example where injectivity of a local function
  -- is used to solve metas.  It fails if we do injectivity analysis
  -- before polarity only.
  checkInjectivity_        names
  checkProjectionLikeness_ names

-- | Check if there is a inferred eta record type in the mutual block.
--   If yes, repeat the record pattern translation for all function definitions
--   in the block.
--   This is necessary since the original record pattern translation will
--   have skipped record patterns of the new record types (as eta was off for them).
--   See issue #2308 (and #2197).
revisitRecordPatternTranslation :: [QName] -> TCM ()
revisitRecordPatternTranslation qs = do
  -- rs: inferred eta record types of this mutual block
  -- qccs: compiled clauses of definitions
  (rs, qccs) <- partitionEithers . catMaybes <$> mapM classify qs
  unless (null rs) $ forM_ qccs $ \(q,cc) -> do
    cc <- translateCompiledClauses cc
    modifySignature $ updateDefinition q $ updateTheDef $
      updateCompiledClauses $ const $ Just cc
  where
  -- Walk through the definitions and return the set of inferred eta record types
  -- and the set of function definitions in the mutual block
  classify q = inConcreteOrAbstractMode q $ \ def -> do
    case theDef def of
      Record{ recEtaEquality' = Inferred True } -> return $ Just $ Left q
      Function
        { funProjection = Nothing
            -- Andreas, 2017-08-10, issue #2664:
            -- Do not record pattern translate record projection definitions!
        , funCompiled   = Just cc
        } -> return $ Just $ Right (q, cc)
      _ -> return Nothing

type FinalChecks = Maybe (TCM ())

checkUnquoteDecl :: Info.MutualInfo -> [Info.DefInfo] -> [QName] -> A.Expr -> TCM FinalChecks
checkUnquoteDecl mi is xs e = do
  reportSDoc "tc.unquote.decl" 20 $ text "Checking unquoteDecl" <+> sep (map prettyTCM xs)
  Nothing <$ unquoteTop xs e

checkUnquoteDef :: [Info.DefInfo] -> [QName] -> A.Expr -> TCM ()
checkUnquoteDef _ xs e = do
  reportSDoc "tc.unquote.decl" 20 $ text "Checking unquoteDef" <+> sep (map prettyTCM xs)
  () <$ unquoteTop xs e

-- | Run a reflected TCM computatation expected to define a given list of
--   names.
unquoteTop :: [QName] -> A.Expr -> TCM [QName]
unquoteTop xs e = do
  tcm   <- primAgdaTCM
  unit  <- primUnit
  lzero <- primLevelZero
  let vArg = defaultArg
      hArg = setHiding Hidden . vArg
  m    <- checkExpr e $ El (mkType 0) $ apply tcm [hArg lzero, vArg unit]
  res  <- runUnquoteM $ tell xs >> evalTCM m
  case res of
    Left err      -> typeError $ UnquoteFailed err
    Right (_, xs) -> return xs

-- | Instantiate all metas in 'Definition' associated to 'QName'.
--   Makes sense after freezing metas. Some checks, like free variable
--   analysis, are not in 'TCM', so they will be more precise (see issue 1099)
--   after meta instantiation.
--   Precondition: name has been added to signature already.
instantiateDefinitionType :: QName -> TCM ()
instantiateDefinitionType q = do
  reportSLn "tc.decl.inst" 20 $ "instantiating type of " ++ prettyShow q
  t  <- defType . fromMaybe __IMPOSSIBLE__ . lookupDefinition q <$> getSignature
  t' <- instantiateFull t
  modifySignature $ updateDefinition q $ updateDefType $ const t'
  reportSDoc "tc.decl.inst" 30 $ vcat
    [ text "  t  = " <+> prettyTCM t
    , text "  t' = " <+> prettyTCM t'
    ]

-- Andreas, 2014-04-11
-- UNUSED, costs a couple of sec on the std-lib
-- -- | Instantiate all metas in 'Definition' associated to 'QName'.
-- --   Makes sense after freezing metas.
-- --   Some checks, like free variable analysis, are not in 'TCM',
-- --   so they will be more precise (see issue 1099) after meta instantiation.
-- --
-- --   Precondition: name has been added to signature already.
-- instantiateDefinition :: QName -> TCM ()
-- instantiateDefinition q = do
--   reportSLn "tc.decl.inst" 20 $ "instantiating " ++ prettyShow q
--   sig <- getSignature
--   let def = fromMaybe __IMPOSSIBLE__ $ lookupDefinition q sig
--   def <- instantiateFull def
--   modifySignature $ updateDefinition q $ const def

-- | Highlight a declaration.
highlight_ :: A.Declaration -> TCM ()
highlight_ d = do
  let highlight d = generateAndPrintSyntaxInfo d Full True
  Bench.billTo [Bench.Highlighting] $ case d of
    A.Axiom{}                -> highlight d
    A.Field{}                -> __IMPOSSIBLE__
    A.Primitive{}            -> highlight d
    A.Mutual i ds            -> mapM_ highlight_ $ deepUnscopeDecls ds
    A.Apply{}                -> highlight d
    A.Import{}               -> highlight d
    A.Pragma{}               -> highlight d
    A.ScopedDecl{}           -> return ()
    A.FunDef{}               -> highlight d
    A.DataDef{}              -> highlight d
    A.DataSig{}              -> highlight d
    A.Open{}                 -> highlight d
    A.PatternSynDef{}        -> highlight d
    A.UnquoteDecl{}          -> highlight d
    A.UnquoteDef{}           -> highlight d
    A.Section i x tel _      -> highlight (A.Section i x tel [])
      -- Each block in the section has already been highlighted,
      -- all that remains is the module declaration.
    A.RecSig{}               -> highlight d
    A.RecDef i x ind eta c ps tel cs ->
      highlight (A.RecDef i x ind eta c [] dummy (fields cs))
      -- The telescope and all record module declarations except
      -- for the fields have already been highlighted.
      where
      fields (A.ScopedDecl _ ds1 : ds2) = fields ds1 ++ fields ds2
      fields (d@A.Field{}        : ds)  = d : fields ds
      fields (_                  : ds)  = fields ds
      fields []                         = []
      -- Andreas, 2016-01-22, issue 1791
      -- The expression denoting the record constructor type
      -- is replace by a dummy expression in order to /not/
      -- generate highlighting from it.
      -- Simply because all the highlighting info is wrong
      -- in the record constructor type:
      -- * fields become bound variables,
      -- * declarations become let-bound variables.
      -- We do not need that crap.
      dummy = A.Lit $ LitString noRange $
        "do not highlight construct(ed/or) type"

-- | Termination check a declaration.
checkTermination_ :: A.Declaration -> TCM ()
checkTermination_ d = Bench.billTo [Bench.Termination] $ do
  reportSLn "tc.decl" 20 $ "checkDecl: checking termination..."
  case d of
      -- Record module definitions should not be termination-checked twice.
      A.RecDef {} -> return ()
      _ -> disableDestructiveUpdate $ do
        termErrs <- termDecl d
        -- If there are some termination errors, we collect them in
        -- the state.
        -- The termination checker already marked non-terminating functions as such.
        unless (null termErrs) $ do
          warning $ TerminationIssue termErrs

-- | Check a set of mutual names for positivity.
checkPositivity_ :: Info.MutualInfo -> Set QName -> TCM ()
checkPositivity_ mi names = Bench.billTo [Bench.Positivity] $ do
  -- Positivity checking.
  reportSLn "tc.decl" 20 $ "checkDecl: checking positivity..."
  checkStrictlyPositive mi names

  -- Andreas, 2012-02-13: Polarity computation uses info from
  -- positivity check, so it needs happen after positivity
  -- check.
  computePolarity $ Set.toList names

-- | Check that all coinductive records are actually recursive.
--   (Otherwise, one can implement invalid recursion schemes just like
--   for the old coinduction.)
checkCoinductiveRecords :: [A.Declaration] -> TCM ()
checkCoinductiveRecords ds = forM_ ds $ \case
  A.RecDef _ q (Just (Ranged r CoInductive)) _ _ _ _ _ -> setCurrentRange r $ do
    unlessM (isRecursiveRecord q) $ typeError $ GenericError $
      "Only recursive records can be coinductive"
  _ -> return ()

-- | Check a set of mutual names for constructor-headedness.
checkInjectivity_ :: Set QName -> TCM ()
checkInjectivity_ names = Bench.billTo [Bench.Injectivity] $ do
  reportSLn "tc.decl" 20 $ "checkDecl: checking injectivity..."
  -- Andreas, 2015-07-01, see Issue1366b:
  -- Injectivity check needs also to be run for abstract definitions.
  -- Fold.forM_ names $ \ q -> ignoreAbstractMode $ do -- NOT NECESSARY after all
  Fold.forM_ names $ \ q -> inConcreteOrAbstractMode q $ \ def -> do
    -- For abstract q, we should be inAbstractMode,
    -- otherwise getConstInfo returns Axiom.
    --
    -- Andreas, 2015-07-01:
    -- Quite surprisingly, inAbstractMode does not allow us to look
    -- at a local definition (@where@ block) of an abstract definition.
    -- This is because the local definition is defined in a strict submodule.
    -- We can only see through abstract definitions in the current module
    -- or super modules inAbstractMode.
    -- I changed that in Monad.Signature.treatAbstractly', so we can see
    -- our own local definitions.
    case theDef def of
      d@Function{ funClauses = cs, funTerminates = term } -> do
        case term of
          Just True -> do
            inv <- checkInjectivity q cs
            modifySignature $ updateDefinition q $ updateTheDef $ const $
              d { funInv = inv }
          _ -> reportSLn "tc.inj.check" 20 $
             prettyShow q ++ " is not verified as terminating, thus, not considered for injectivity"
      _ -> do
        abstr <- asks envAbstractMode
        reportSLn "tc.inj.check" 20 $
          "we are in " ++ show abstr ++ " and " ++
             prettyShow q ++ " is abstract or not a function, thus, not considered for injectivity"

-- | Check a set of mutual names for projection likeness.
--
--   Only a single, non-abstract function can be projection-like.
--   Making an abstract function projection-like would break the
--   invariant that the type of the principle argument of a projection-like
--   function is always inferable.

checkProjectionLikeness_ :: Set QName -> TCM ()
checkProjectionLikeness_ names = Bench.billTo [Bench.ProjectionLikeness] $ do
      -- Non-mutual definitions can be considered for
      -- projection likeness
      let ds = Set.toList names
      reportSLn "tc.proj.like" 20 $ "checkDecl: checking projection-likeness of " ++ prettyShow ds
      case ds of
        [d] -> do
          def <- getConstInfo d
          -- For abstract identifiers, getConstInfo returns Axiom.
          -- Thus, abstract definitions are not considered for projection-likeness.
          case theDef def of
            Function{} -> makeProjection (defName def)
            _          -> reportSLn "tc.proj.like" 25 $
              prettyShow d ++ " is abstract or not a function, thus, not considered for projection-likeness"
        _ -> reportSLn "tc.proj.like" 25 $
               "mutual definitions are not considered for projection-likeness"

-- | Freeze metas created by given computation if in abstract mode.
whenAbstractFreezeMetasAfter :: Info.DefInfo -> TCM a -> TCM a
whenAbstractFreezeMetasAfter Info.DefInfo{ defAccess, defAbstract} m = do
  let pubAbs = defAccess == PublicAccess && defAbstract == AbstractDef
  if not pubAbs then m else do
    (a, ms) <- metasCreatedBy m
    xs <- freezeMetas' $ (`Set.member` ms)
    reportSDoc "tc.decl.ax" 20 $ vcat
      [ text "Abstract type signature produced new metas: " <+> sep (map prettyTCM $ Set.toList ms)
      , text "We froze the following ones of these:       " <+> sep (map prettyTCM xs)
      ]
    return a

-- | Type check an axiom.
checkAxiom :: A.Axiom -> Info.DefInfo -> ArgInfo ->
              Maybe [Occurrence] -> QName -> A.Expr -> TCM ()
checkAxiom funSig i info0 mp x e = whenAbstractFreezeMetasAfter i $ do
  -- Andreas, 2016-07-19 issues #418 #2102:
  -- We freeze metas in type signatures of abstract definitions, to prevent
  -- leakage of implementation details.

  -- Andreas, 2012-04-18  if we are in irrelevant context, axioms is irrelevant
  -- even if not declared as such (Issue 610).
  rel <- max (getRelevance info0) <$> asks envRelevance
  let info = setRelevance rel info0
  -- rel <- ifM ((Irrelevant ==) <$> asks envRelevance) (return Irrelevant) (return rel0)
  t <- workOnTypes $ isType_ e
  reportSDoc "tc.decl.ax" 10 $ sep
    [ text $ "checked type signature"
    , nest 2 $ prettyTCM rel <> prettyTCM x <+> text ":" <+> prettyTCM t
    , nest 2 $ text "of sort " <+> prettyTCM (getSort t)
    ]

  -- Andreas, 2015-03-17 Issue 1428: Do not postulate sizes in parametrized
  -- modules!
  when (funSig == A.NoFunSig) $ do
    whenM ((== SizeUniv) <$> do reduce $ getSort t) $ do
      whenM ((> 0) <$> getContextSize) $ do
        typeError $ GenericError $ "We don't like postulated sizes in parametrized modules."

  -- Ensure that polarity pragmas do not contain too many occurrences.
  (occs, pols) <- case mp of
    Nothing   -> return ([], [])
    Just occs -> do
      TelV tel _ <- telView t
      let n = length (telToList tel)
      when (n < length occs) $
        typeError $ TooManyPolarities x n
      let pols = map polFromOcc occs
      reportSLn "tc.polarity.pragma" 10 $
        "Setting occurrences and polarity for " ++ prettyShow x ++ ":\n  " ++
        prettyShow occs ++ "\n  " ++ prettyShow pols
      return (occs, pols)

  -- Not safe. See Issue 330
  -- t <- addForcingAnnotations t
  addConstant x =<< do
    useTerPragma $
      (defaultDefn info x t $
         case funSig of
           A.FunSig   -> set funMacro (Info.defMacro i == MacroDef) emptyFunction
           A.NoFunSig -> Axiom)   -- NB: used also for data and record type sigs
        { defArgOccurrences = occs
        , defPolarity       = pols
        }

  -- Add the definition to the instance table, if needed
  when (Info.defInstance i == InstanceDef) $ do
    addTypedInstance x t

  traceCall (IsType_ e) $ do -- need Range for error message
    -- Andreas, 2016-06-21, issue #2054
    -- Do not default size metas to ∞ in local type signatures
    checkingWhere <- asks envCheckingWhere
    solveSizeConstraints $ if checkingWhere then DontDefaultToInfty else DefaultToInfty

  -- Andreas, 2011-05-31, that freezing below is probably wrong:
  -- when_ (Info.defAbstract i == AbstractDef) $ freezeMetas

-- | Type check a primitive function declaration.
checkPrimitive :: Info.DefInfo -> QName -> A.Expr -> TCM ()
checkPrimitive i x e =
    traceCall (CheckPrimitive (getRange i) (qnameName x) e) $ do  -- TODO!! (qnameName)
    (name, PrimImpl t' pf) <- lookupPrimitiveFunctionQ x
    -- Primitive functions on nats are BUILTIN not 'primitive'
    let builtinPrimitives =
          [ "primNatPlus", "primNatMinus" , "primNatTimes"
          , "primNatDivSucAux", "primNatModSucAux"
          , "primNatEquality", "primNatLess" ]
    when (elem name builtinPrimitives) $ typeError $ NoSuchPrimitiveFunction name
    t <- isType_ e
    noConstraints $ equalType t t'
    let s  = prettyShow $ qnameName x
    bindPrimitive s pf
    addConstant x $
      defaultDefn defaultArgInfo x t $
        Primitive (Info.defAbstract i) s [] Nothing

assertCurrentModule :: QName -> String -> TCM ()
assertCurrentModule x err =
  do def <- getConstInfo x
     m <- currentModule
     let m' = qnameModule $ defName def
     unless (m == m' || isSubModuleOf m' m) $ typeError $ GenericError err

-- | Check a pragma.
checkPragma :: Range -> A.Pragma -> TCM ()
checkPragma r p =
    traceCall (CheckPragma r p) $ case p of
        A.BuiltinPragma x e -> bindBuiltin x e
        A.BuiltinNoDefPragma b x -> bindBuiltinNoDef b x
        A.RewritePragma q   -> addRewriteRule q
        A.CompiledTypePragma x hs -> do
          def <- getConstInfo x
          case theDef def of
            Axiom{} -> addHaskellType x hs
            _       -> typeError $ GenericError
                        "COMPILED_TYPE directive only works on postulates"
        A.CompiledDataPragma x hs hcs -> do
          def <- getConstInfo x
          -- Check that the pragma appears in the same module
          -- as the datatype.
          assertCurrentModule x $
              "COMPILED_DATA directives must appear in the same module " ++
              "as their corresponding datatype definition,"
          case theDef def of
            Datatype{dataCons = cs} -> addHaskellData x hs hcs
            Record{recConHead = ch} -> addHaskellData x hs hcs
            _ -> typeError $ GenericError "COMPILED_DATA on non datatype"
        A.CompilePragma b x s -> do
          assertCurrentModule x $
              "COMPILE pragmas must appear in the same module " ++
              "as their corresponding definitions,"
          addPragma b x s
        A.CompiledPragma x hs -> do
          def <- getConstInfo x
          let addCompiled = addHaskellCode x hs
          case theDef def of
            Axiom{} -> addCompiled
            Function{} -> addCompiled
            _   -> typeError $ GenericError "COMPILED directive only works on postulates and functions"

        A.CompiledExportPragma x hs -> do
          def <- getConstInfo x
          let correct = case theDef def of
                            Function{} -> True
                            Constructor{} -> False
                            _   -> False
          if not correct
            then typeError $ GenericError "COMPILED_EXPORT directive only works on functions"
            else addHaskellExport x hs
        A.CompiledJSPragma x ep ->
          addJSCode x ep
        A.CompiledUHCPragma x cr -> do
          def <- getConstInfo x
          case theDef def of
            Axiom{} -> addCoreCode x cr
            _ -> typeError $ GenericError "COMPILED_UHC directive only works on postulates" -- only allow postulates for the time being
        A.CompiledDataUHCPragma x crd crcs -> do
          -- TODO mostly copy-paste from the CompiledDataPragma, should be refactored into a seperate function
          def <- getConstInfo x
          -- Check that the pragma appears in the same module
          -- as the datatype.
          m <- currentModule
          let m' = qnameModule $ defName def
          unless (m == m') $ typeError $ GenericError $
              "COMPILED_DATA_UHC directives must appear in the same module " ++
              "as their corresponding datatype definition,"
          case theDef def of
            Datatype{dataCons = cs} -> addCoreType x crd crcs
            _ -> typeError $ GenericError "COMPILED_DATA_UHC on non datatype"
        A.StaticPragma x -> do
          def <- getConstInfo x
          case theDef def of
            Function{} -> markStatic x
            _          -> typeError $ GenericError "STATIC directive only works on functions"
        A.InjectivePragma x -> markInjective x
        A.InlinePragma x -> do
          def <- getConstInfo x
          case theDef def of
            Function{} -> markInline x
            _          -> typeError $ GenericError "INLINE directive only works on functions"
        A.OptionsPragma{} -> typeError $ GenericError $ "OPTIONS pragma only allowed at beginning of file, before top module declaration"
        A.DisplayPragma f ps e -> checkDisplayPragma f ps e
        A.EtaPragma r -> do
          let noRecord = typeError $ GenericError $
                "ETA pragma is only applicable to coinductive records"
          caseMaybeM (isRecord r) noRecord $ \case
            Record{ recInduction = ind, recEtaEquality' = eta } -> do
              unless (ind == Just CoInductive) $ noRecord
              when (eta == Specified False) $ typeError $ GenericError $
                "ETA pragram conflicts with no-eta-equality declaration"
            _ -> __IMPOSSIBLE__
          modifySignature $ updateDefinition r $ updateTheDef $ \case
            def@Record{} -> def { recEtaEquality' = Specified True }
            _ -> __IMPOSSIBLE__

-- | Type check a bunch of mutual inductive recursive definitions.
--
-- All definitions which have so far been assigned to the given mutual
-- block are returned.
checkMutual :: Info.MutualInfo -> [A.Declaration] -> TCM (MutualId, Set QName)
checkMutual i ds = inMutualBlock $ \ blockId -> do

  verboseS "tc.decl.mutual" 20 $ do
    reportSDoc "tc.decl.mutual" 20 $ vcat $
      (text "Checking mutual block" <+> text (show blockId) <> text ":") :
      map (nest 2 . prettyA) ds

  insertMutualBlockInfo blockId i
  local (\e -> e { envTerminationCheck = () <$ Info.mutualTermCheck i }) $
    mapM_ checkDecl ds

  (blockId, ) . mutualNames <$> lookupMutualBlock blockId

-- | Type check the type signature of an inductive or recursive definition.
checkTypeSignature :: A.TypeSignature -> TCM ()
checkTypeSignature (A.ScopedDecl scope ds) = do
  setScope scope
  mapM_ checkTypeSignature ds
checkTypeSignature (A.Axiom funSig i info mp x e) =
  Bench.billTo [Bench.Definition x] $
  Bench.billTo [Bench.Typing, Bench.TypeSig] $
    let abstr = case Info.defAccess i of
          PrivateAccess{}
            | Info.defAbstract i == AbstractDef -> inAbstractMode
              -- Issue #2321, only go to AbstractMode for abstract definitions
            | otherwise -> inConcreteMode
          PublicAccess  -> inConcreteMode
          OnlyQualified -> __IMPOSSIBLE__
    in abstr $ checkAxiom funSig i info mp x e
checkTypeSignature _ = __IMPOSSIBLE__   -- type signatures are always axioms


-- | Type check a module.

checkSection :: Info.ModuleInfo -> ModuleName -> A.Telescope -> [A.Declaration] -> TCM ()
checkSection _ x tel ds = newSection x tel $ mapM_ checkDeclCached ds


-- | Helper for 'checkSectionApplication'.
--
--   Matches the arguments of the module application with the
--   module parameters.
--
--   Returns the remaining module parameters as an open telescope.
--   Warning: the returned telescope is /not/ the final result,
--   an actual instantiation of the parameters does not occur.
checkModuleArity
  :: ModuleName           -- ^ Name of applied module.
  -> Telescope            -- ^ The module parameters.
  -> [NamedArg A.Expr]  -- ^ The arguments this module is applied to.
  -> TCM Telescope        -- ^ The remaining module parameters (has free de Bruijn indices!).
checkModuleArity m tel args = check tel args
  where
    bad = typeError $ ModuleArityMismatch m tel args

    check tel []             = return tel
    check EmptyTel (_:_)     = bad
    check (ExtendTel (Dom info _) btel) args0@(Arg info' (Named rname _) : args) =
      let name = fmap rangedThing rname
          y    = absName btel
          tel  = absBody btel in
      case (argInfoHiding info, argInfoHiding info', name) of
        (Instance{}, NotHidden, _)        -> check tel args0
        (Instance{}, Hidden, _)           -> check tel args0
        (Instance{}, Instance{}, Nothing) -> check tel args
        (Instance{}, Instance{}, Just x)
          | x == y                        -> check tel args
          | otherwise                     -> check tel args0
        (Hidden, NotHidden, _)            -> check tel args0
        (Hidden, Instance{}, _)           -> check tel args0
        (Hidden, Hidden, Nothing)         -> check tel args
        (Hidden, Hidden, Just x)
          | x == y                        -> check tel args
          | otherwise                     -> check tel args0
        (NotHidden, NotHidden, _)         -> check tel args
        (NotHidden, Hidden, _)            -> bad
        (NotHidden, Instance{}, _)        -> bad

-- | Check an application of a section (top-level function, includes @'traceCall'@).
checkSectionApplication
  :: Info.ModuleInfo
  -> ModuleName          -- ^ Name @m1@ of module defined by the module macro.
  -> A.ModuleApplication -- ^ The module macro @λ tel → m2 args@.
  -> A.ScopeCopyInfo     -- ^ Imported names and modules
  -> TCM ()
checkSectionApplication i m1 modapp copyInfo =
  traceCall (CheckSectionApplication (getRange i) m1 modapp) $
  checkSectionApplication' i m1 modapp copyInfo

-- | Check an application of a section.
checkSectionApplication'
  :: Info.ModuleInfo
  -> ModuleName          -- ^ Name @m1@ of module defined by the module macro.
  -> A.ModuleApplication -- ^ The module macro @λ tel → m2 args@.
  -> A.ScopeCopyInfo     -- ^ Imported names and modules
  -> TCM ()
checkSectionApplication' i m1 (A.SectionApp ptel m2 args) copyInfo = do
  -- Module applications can appear in lets, in which case we treat
  -- lambda-bound variables as additional parameters to the module.
  extraParams <- do
    mfv <- getCurrentModuleFreeVars
    fv  <- getContextSize
    return (fv - mfv)
  when (extraParams > 0) $ reportSLn "tc.mod.apply" 30 $ "Extra parameters to " ++ prettyShow m1 ++ ": " ++ show extraParams
  -- Type-check the LHS (ptel) of the module macro.
  checkTelescope ptel $ \ ptel -> do
    -- We are now in the context @ptel@.
    -- Get the correct parameter telescope of @m2@.
    tel <- lookupSection m2
    vs  <- moduleParamsToApply $ qnameModule $ mnameToQName m2
    let tel'  = apply tel vs
    -- Compute the remaining parameter telescope after stripping of
    -- the initial parameters that are determined by the @args@.
    -- Warning: @etaTel@ is not well-formed in @ptel@, since
    -- the actual application has not happened.
    etaTel <- checkModuleArity m2 tel' args
    -- Take the module parameters that will be instantiated by @args@.
    let tel'' = telFromList $ take (size tel' - size etaTel) $ telToList tel'
    reportSDoc "tc.mod.apply" 15 $ vcat
      [ text "applying section" <+> prettyTCM m2
      , nest 2 $ text "args =" <+> sep (map prettyA args)
      , nest 2 $ text "ptel =" <+> escapeContext (size ptel) (prettyTCM ptel)
      , nest 2 $ text "tel  =" <+> prettyTCM tel
      , nest 2 $ text "tel' =" <+> prettyTCM tel'
      , nest 2 $ text "tel''=" <+> prettyTCM tel''
      , nest 2 $ text "eta  =" <+> escapeContext (size ptel) (addContext tel'' $ prettyTCM etaTel)
      ]
    -- Now, type check arguments.
    ts <- (noConstraints $ checkArguments_ DontExpandLast (getRange i) args tel') >>= \case
      (ts, etaTel') | (size etaTel == size etaTel') -> return ts
      _ -> __IMPOSSIBLE__
    -- Perform the application of the module parameters.
    let aTel = tel' `apply` ts
    reportSDoc "tc.mod.apply" 15 $ vcat
      [ nest 2 $ text "aTel =" <+> prettyTCM aTel
      ]
    -- Andreas, 2014-04-06, Issue 1094:
    -- Add the section with well-formed telescope.
    addContext (KeepNames aTel) $ do
      reportSDoc "tc.mod.apply" 80 $
        text "addSection" <+> prettyTCM m1 <+> (getContextTelescope >>= \ tel -> inTopContext (prettyTCM tel))
      addSection m1

    reportSDoc "tc.mod.apply" 20 $ vcat
      [ sep [ text "applySection", prettyTCM m1, text "=", prettyTCM m2, fsep $ map prettyTCM (vs ++ ts) ]
      , nest 2 $ pretty copyInfo
      ]
    args <- instantiateFull $ vs ++ ts
    let n = size aTel
    etaArgs <- inTopContext $ addContext aTel getContextArgs
    addContext' (KeepNames aTel) $
      applySection m1 (ptel `abstract` aTel) m2 (raise n args ++ etaArgs) copyInfo

checkSectionApplication' i m1 (A.RecordModuleIFS x) copyInfo = do
  let name = mnameToQName x
  tel' <- lookupSection x
  vs   <- moduleParamsToApply $ qnameModule name
  let tel = tel' `apply` vs
      args = teleArgs tel

      telInst :: Telescope
      telInst = instFinal tel

      -- Locate last (rightmost) parameter and make it @Instance@.
      instFinal :: Telescope -> Telescope
      -- Telescopes do not have @NoAbs@.
      instFinal (ExtendTel _ NoAbs{}) = __IMPOSSIBLE__
      -- Found last parameter: switch it to @Instance@.
      instFinal (ExtendTel (Dom info t) (Abs n EmptyTel)) =
                 ExtendTel (Dom ifo' t) (Abs n EmptyTel)
        where ifo' = makeInstance info
      -- Otherwise, keep searching for last parameter:
      instFinal (ExtendTel arg (Abs n tel)) =
                 ExtendTel arg (Abs n (instFinal tel))
      -- Before instFinal is invoked, we have checked that the @tel@ is not empty.
      instFinal EmptyTel = __IMPOSSIBLE__

  reportSDoc "tc.mod.apply" 20 $ vcat
    [ sep [ text "applySection", prettyTCM name, text "{{...}}" ]
    , nest 2 $ text "x       =" <+> prettyTCM x
    , nest 2 $ text "name    =" <+> prettyTCM name
    , nest 2 $ text "tel     =" <+> prettyTCM tel
    , nest 2 $ text "telInst =" <+> prettyTCM telInst
    , nest 2 $ text "vs      =" <+> sep (map prettyTCM vs)
    -- , nest 2 $ text "args    =" <+> sep (map prettyTCM args)
    ]
  reportSDoc "tc.mod.apply" 60 $ vcat
    [ nest 2 $ text "vs      =" <+> text (show vs)
    -- , nest 2 $ text "args    =" <+> text (show args)
    ]
  when (tel == EmptyTel) $
    typeError $ GenericError $ prettyShow (qnameToConcrete name) ++ " is not a parameterised section"

  addContext' telInst $ do
    vs <- moduleParamsToApply $ qnameModule name
    reportSDoc "tc.mod.apply" 20 $ vcat
      [ nest 2 $ text "vs      =" <+> sep (map prettyTCM vs)
      , nest 2 $ text "args    =" <+> sep (map (parens . prettyTCM) args)
      ]
    reportSDoc "tc.mod.apply" 60 $ vcat
      [ nest 2 $ text "vs      =" <+> text (show vs)
      , nest 2 $ text "args    =" <+> text (show args)
      ]
    addSection m1
    applySection m1 telInst x (vs ++ args) copyInfo

-- | Type check an import declaration. Actually doesn't do anything, since all
--   the work is done when scope checking.
checkImport :: Info.ModuleInfo -> ModuleName -> TCM ()
checkImport i x = return ()

------------------------------------------------------------------------
-- * Debugging
------------------------------------------------------------------------

class ShowHead a where
  showHead :: a -> String

instance ShowHead A.Declaration where
  showHead d =
    case d of
      A.Axiom        {} -> "Axiom"
      A.Field        {} -> "Field"
      A.Primitive    {} -> "Primitive"
      A.Mutual       {} -> "Mutual"
      A.Section      {} -> "Section"
      A.Apply        {} -> "Apply"
      A.Import       {} -> "Import"
      A.Pragma       {} -> "Pragma"
      A.Open         {} -> "Open"
      A.FunDef       {} -> "FunDef"
      A.DataSig      {} -> "DataSig"
      A.DataDef      {} -> "DataDef"
      A.RecSig       {} -> "RecSig"
      A.RecDef       {} -> "RecDef"
      A.PatternSynDef{} -> "PatternSynDef"
      A.UnquoteDecl  {} -> "UnquoteDecl"
      A.ScopedDecl   {} -> "ScopedDecl"
      A.UnquoteDef   {} -> "UnquoteDef"

debugPrintDecl :: A.Declaration -> TCM ()
debugPrintDecl d = do
    verboseS "tc.decl" 45 $ do
      reportSLn "tc.decl" 45 $ "checking a " ++ showHead d
      case d of
        A.Section info mname tel ds -> do
          reportSLn "tc.decl" 45 $
            "section " ++ prettyShow mname ++ " has "
              ++ show (length tel) ++ " parameters and "
              ++ show (length ds) ++ " declarations"
          reportSDoc "tc.decl" 45 $ prettyA $ A.Section info mname tel []
          forM_ ds $ \ d -> do
            reportSDoc "tc.decl" 45 $ prettyA d
        _ -> return ()
