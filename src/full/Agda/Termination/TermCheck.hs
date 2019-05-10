{-# LANGUAGE BangPatterns               #-}
{-# LANGUAGE GADTs                      #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE ImplicitParams             #-}
{-# LANGUAGE NondecreasingIndentation   #-}

{- Checking for Structural recursion
   Authors: Andreas Abel, Nils Anders Danielsson, Ulf Norell,
              Karl Mehltretter and others
   Created: 2007-05-28
   Source : TypeCheck.Rules.Decl
 -}

module Agda.Termination.TermCheck
    ( termDecl
    , termMutual
    , Result
    ) where

import Prelude hiding ( null )

import Control.Applicative hiding (empty)
import Control.Monad.Reader
import Control.Monad.State

import Data.Foldable (toList)
import qualified Data.List as List
import Data.Monoid hiding ((<>))
import qualified Data.Set as Set
import Data.Traversable (Traversable, traverse)

import Agda.Syntax.Abstract (IsProjP(..), AllNames(..))
import qualified Agda.Syntax.Abstract as A
import Agda.Syntax.Internal as I
import Agda.Syntax.Internal.Pattern as I
import Agda.Syntax.Internal.Generic
import qualified Agda.Syntax.Info as Info
import Agda.Syntax.Position
import Agda.Syntax.Common
import Agda.Syntax.Translation.InternalToAbstract ( reifyPatterns )

import Agda.Termination.CutOff
import Agda.Termination.Monad
import Agda.Termination.CallGraph hiding (toList)
import qualified Agda.Termination.CallGraph as CallGraph
import Agda.Termination.CallMatrix hiding (toList)
import Agda.Termination.Order     as Order
import qualified Agda.Termination.SparseMatrix as Matrix
import Agda.Termination.Termination (endos, idempotent)
import qualified Agda.Termination.Termination  as Term
import Agda.Termination.RecCheck
import Agda.Termination.Inlining

import Agda.TypeChecking.Datatypes
import Agda.TypeChecking.EtaContract
import Agda.TypeChecking.Functions
import Agda.TypeChecking.Monad
import Agda.TypeChecking.Monad.Builtin
import Agda.TypeChecking.Positivity.Occurrence
import Agda.TypeChecking.Pretty
import Agda.TypeChecking.Records -- (isRecordConstructor, isInductiveRecord)
import Agda.TypeChecking.Reduce (reduce, normalise, instantiate, instantiateFull)
import Agda.TypeChecking.SizedTypes
import Agda.TypeChecking.Substitute
import Agda.TypeChecking.Telescope

import qualified Agda.Benchmarking as Benchmark
import Agda.TypeChecking.Monad.Benchmark (billTo, billPureTo)

import Agda.Interaction.Options

import Agda.Utils.Either
import Agda.Utils.Function
import Agda.Utils.Functor
import Agda.Utils.List
import Agda.Utils.Size
import Agda.Utils.Maybe
import Agda.Utils.Monad -- (mapM', forM', ifM, or2M, and2M)
import Agda.Utils.Null
import Agda.Utils.Permutation
import Agda.Utils.Pretty (prettyShow)
import Agda.Utils.Singleton
import qualified Agda.Utils.VarSet as VarSet

import Agda.Utils.Impossible

-- | Call graph with call info for composed calls.

type Calls = CallGraph CallPath

-- | The result of termination checking a module.
--   Must be a 'Monoid' and have 'Singleton'.

type Result = [TerminationError]

-- | Entry point: Termination check a single declaration.
--
--   Precondition: 'envMutualBlock' must be set correctly.

termDecl :: A.Declaration -> TCM Result
termDecl d = inTopContext $ termDecl' d


-- | Termination check a single declaration
--   (without necessarily ignoring @abstract@).

termDecl' :: A.Declaration -> TCM Result
termDecl' d = case d of
    A.Axiom {}            -> return mempty
    A.Field {}            -> return mempty
    A.Primitive {}        -> return mempty
    A.Mutual i ds         -> termMutual $ getNames ds
    A.Section _ _ _ ds    -> termDecls ds
        -- section structure can be ignored as we are termination checking
        -- definitions lifted to the top-level
    A.Apply {}            -> return mempty
    A.Import {}           -> return mempty
    A.Pragma {}           -> return mempty
    A.Open {}             -> return mempty
    A.PatternSynDef {}    -> return mempty
    A.Generalize {}       -> return mempty
        -- open, pattern synonym and generalize defs are just artifacts from the concrete syntax
    A.ScopedDecl scope ds -> {- withScope_ scope $ -} termDecls ds
        -- scope is irrelevant as we are termination checking Syntax.Internal
    A.RecSig{}            -> return mempty
    A.RecDef _ r _ _ _ _ _ _ ds -> termDecls ds
    -- These should all be wrapped in mutual blocks
    A.FunDef{}      -> __IMPOSSIBLE__
    A.DataSig{}     -> __IMPOSSIBLE__
    A.DataDef{}     -> __IMPOSSIBLE__
    A.UnquoteDecl{} -> __IMPOSSIBLE__
    A.UnquoteDef{}  -> __IMPOSSIBLE__
  where
    termDecls ds = concat <$> mapM termDecl' ds

    unscopeDefs = concatMap unscopeDef

    unscopeDef (A.ScopedDecl _ ds) = unscopeDefs ds
    unscopeDef d = [d]

    -- The mutual names mentioned in the abstract syntax
    -- for symbols that need to be termination-checked.
    getNames = concatMap getName
    getName (A.FunDef i x delayed cs)   = [x]
    getName (A.RecDef _ _ _ _ _ _ _ _ ds) = getNames ds
    getName (A.Mutual _ ds)             = getNames ds
    getName (A.Section _ _ _ ds)        = getNames ds
    getName (A.ScopedDecl _ ds)         = getNames ds
    getName (A.UnquoteDecl _ _ xs _)    = xs
    getName (A.UnquoteDef _ xs _)       = xs
    getName _                           = []


-- | Entry point: Termination check the current mutual block.

termMutual
  :: [QName]
     -- ^ The function names defined in this block on top-level.
     --   (For error-reporting only.)
  -> TCM Result
termMutual names0 = ifNotM (optTerminationCheck <$> pragmaOptions) (return mempty) $ {-else-}
 inTopContext $ do

  -- Get set of mutually defined names from the TCM.
  -- This includes local and auxiliary functions introduced
  -- during type-checking.
  mid <- fromMaybe __IMPOSSIBLE__ <$> asksTC envMutualBlock
  mutualBlock <- lookupMutualBlock mid
  let allNames = filter (not . isAbsurdLambdaName) $ Set.elems $ mutualNames mutualBlock
      names    = if null names0 then allNames else names0
      i        = mutualInfo mutualBlock
      -- Andreas, 2014-03-26
      -- Keeping recursion check after experiments on the standard lib.
      -- Seems still to save 1s.
      -- skip = return False
      -- No need to term-check if the declarations are acyclic!
      skip = not <$> do
        -- Andreas, 2016-10-01 issue #2231
        -- Recursivity checker has to see through abstract definitions!
        ignoreAbstractMode $ do
        billTo [Benchmark.Termination, Benchmark.RecCheck] $ recursive allNames
      -- -- Andreas, 2017-03-24, use positivity info to skip non-recursive functions
      -- skip = ignoreAbstractMode $ allM allNames $ \ x -> do
      --   null <$> getMutual x
      -- PROBLEMS with test/Succeed/AbstractCoinduction.agda

  -- We set the range to avoid panics when printing error messages.
  setCurrentRange i $ do

  -- The following debug statement is part of a test case for Issue
  -- #3590.
  reportSLn "term.mutual.id" 40 $
    "Termination checking mutual block " ++ show mid
  reportSLn "term.mutual" 10 $ "Termination checking " ++ prettyShow allNames

  -- NO_TERMINATION_CHECK
  if (Info.mutualTermCheck i `elem` [ NoTerminationCheck, Terminating ]) then do
      reportSLn "term.warn.yes" 10 $ "Skipping termination check for " ++ prettyShow names
      forM_ allNames $ \ q -> setTerminates q True -- considered terminating!
      return mempty
  -- NON_TERMINATING
    else if (Info.mutualTermCheck i == NonTerminating) then do
      reportSLn "term.warn.yes" 10 $ "Considering as non-terminating: " ++ prettyShow names
      forM_ allNames $ \ q -> setTerminates q False
      return mempty
  -- Trivially terminating (non-recursive)
    else ifM skip (do
      reportSLn "term.warn.yes" 10 $ "Trivially terminating: " ++ prettyShow names
      forM_ allNames $ \ q -> setTerminates q True
      return mempty)
   $ {- else -} do

     -- Set the mutual names in the termination environment.
     let setNames e = e
           { terMutual    = allNames
           , terUserNames = names
           }
         runTerm cont = runTerDefault $ do
           cutoff <- terGetCutOff
           reportSLn "term.top" 10 $ "Termination checking " ++ prettyShow names ++
             " with cutoff=" ++ show cutoff ++ "..."
           terLocal setNames cont

     -- New check currently only makes a difference for copatterns.
     -- Since it is slow, only invoke it if
     -- any of the definitions uses copatterns.
     res <- ifM (orM $ map usesCopatterns allNames)
         -- Then: New check, one after another.
         (runTerm $ forM' allNames $ termFunction)
         -- Else: Old check, all at once.
         (runTerm $ termMutual')

     -- Record result of termination check in signature.
     -- If there are some termination errors, we collect them in
     -- the state and mark the definition as non-terminating so
     -- that it does not get unfolded
     let terminates = null res
     forM_ allNames $ \ q -> setTerminates q terminates
     return res

-- | @termMutual'@ checks all names of the current mutual block,
--   henceforth called @allNames@, for termination.
--
--   @allNames@ is taken from 'Internal' syntax, it contains also
--   the definitions created by the type checker (e.g., with-functions).

termMutual' :: TerM Result
termMutual' = do

  -- collect all recursive calls in the block
  allNames <- terGetMutual
  let collect = forM' allNames termDef

  -- first try to termination check ignoring the dot patterns
  calls1 <- collect
  reportCalls "no " calls1

  cutoff <- terGetCutOff
  let ?cutoff = cutoff
  r <- billToTerGraph $ Term.terminates calls1
  r <- case r of
         r@Right{} -> return r
         Left{}    -> do
           -- Try again, but include the dot patterns this time.
           calls2 <- terSetUseDotPatterns True $ collect
           reportCalls "" calls2
           billToTerGraph $ Term.terminates calls2

  -- @names@ is taken from the 'Abstract' syntax, so it contains only
  -- the names the user has declared.  This is for error reporting.
  names <- terGetUserNames
  case r of
    Left calls -> return $ singleton $ terminationError names $ callInfos calls
    Right{} -> do
      liftTCM $ reportSLn "term.warn.yes" 2 $
        prettyShow (names) ++ " does termination check"
      return mempty

-- | Smart constructor for 'TerminationError'.
--   Removes 'termErrFunctions' that are not mentioned in 'termErrCalls'.
terminationError :: [QName] -> [CallInfo] -> TerminationError
terminationError names calls = TerminationError names' calls
  where names' = names `List.intersect` toList (allNames calls)

billToTerGraph :: a -> TerM a
billToTerGraph a = liftTCM $ billPureTo [Benchmark.Termination, Benchmark.Graph] a

-- | @reportCalls@ for debug printing.
--
--   Replays the call graph completion for debugging.

reportCalls :: String -> Calls -> TerM ()
reportCalls no calls = do
  cutoff <- terGetCutOff
  let ?cutoff = cutoff

  -- We work in TCM exclusively.
  liftTCM $ do

    reportS "term.lex" 20 $ unlines
      [ "Calls (" ++ no ++ "dot patterns): " ++ prettyShow calls
      ]

    -- Print the whole completion phase.
    verboseS "term.matrices" 40 $ do
      let header s = unlines
            [ replicate n '='
            , replicate k '=' ++ s ++ replicate k' '='
            , replicate n '='
            ]
            where n  = 70
                  r  = n - length s
                  k  = r `div` 2
                  k' = r - k
      let report s cs = reportSDoc "term.matrices" 40 $ vcat
            [ text   $ header s
            , nest 2 $ pretty cs
            ]
          cs0     = calls
          step cs = do
            let (new, cs') = completionStep cs0 cs
            report " New call matrices " new
            return $ if null new then Left () else Right cs'
      report " Initial call matrices " cs0
      trampolineM step cs0

    -- Print the result of completion.
    let calls' = CallGraph.complete calls
        idems = filter idempotent $ endos $ CallGraph.toList calls'
    -- TODO
    -- reportSDoc "term.behaviours" 20 $ vcat
    --   [ text $ "Recursion behaviours (" ++ no ++ "dot patterns):"
    --   , nest 2 $ return $ Term.prettyBehaviour calls'
    --   ]
    reportSDoc "term.matrices" 30 $ vcat
      [ text $ "Idempotent call matrices (" ++ no ++ "dot patterns):\n"
      , nest 2 $ vcat $ punctuate "\n" $ map pretty idems
      ]
    -- reportSDoc "term.matrices" 30 $ vcat
    --   [ text $ "Other call matrices (" ++ no ++ "dot patterns):"
    --   , nest 2 $ pretty $ CallGraph.fromList others
    --   ]
    return ()

-- | @termFunction name@ checks @name@ for termination.

termFunction :: QName -> TerM Result
termFunction name = do

  -- Function @name@ is henceforth referred to by its @index@
  -- in the list of @allNames@ of the mutual block.

  allNames <- terGetMutual
  let index = fromMaybe __IMPOSSIBLE__ $ List.elemIndex name allNames

  -- Retrieve the target type of the function to check.

  target <- liftTCM $ do typeEndsInDef =<< typeOfConst name
  reportTarget target
  terSetTarget target $ do

    -- Collect the recursive calls in the block which (transitively)
    -- involve @name@,
    -- taking the target of @name@ into account for computing guardedness.

    let collect = (`trampolineM` (Set.singleton index, mempty, mempty)) $ \ (todo, done, calls) -> do
          if null todo then return $ Left calls else do
            -- Extract calls originating from indices in @todo@.
            new <- forM' todo $ \ i ->
              termDef $ fromMaybe __IMPOSSIBLE__ $ allNames !!! i
            -- Mark those functions as processed and add the calls to the result.
            let done'  = done `mappend` todo
                calls' = new  `mappend` calls
            -- Compute the new todo list:
                todo' = CallGraph.targetNodes new Set.\\ done'
            -- Jump the trampoline.
            return $ Right (todo', done', calls')

    -- First try to termination check ignoring the dot patterns
    calls1 <- terSetUseDotPatterns False $ collect
    reportCalls "no " calls1

    r <- do
     cutoff <- terGetCutOff
     let ?cutoff = cutoff
     r <- billToTerGraph $ Term.terminatesFilter (== index) calls1
     case r of
       Right () -> return $ Right ()
       Left{}    -> do
         -- Try again, but include the dot patterns this time.
         calls2 <- terSetUseDotPatterns True $ collect
         reportCalls "" calls2
         billToTerGraph $ mapLeft callInfos $ Term.terminatesFilter (== index) calls2

    names <- terGetUserNames
    case r of
      Left calls -> return $ singleton $ terminationError ([name] `List.intersect` names) calls
      Right () -> do
        liftTCM $ reportSLn "term.warn.yes" 2 $
          prettyShow name ++ " does termination check"
        return mempty
   where
     reportTarget r = liftTCM $
       reportSLn "term.target" 20 $ "  target type " ++
         caseMaybe r "not recognized" (\ q ->
           "ends in " ++ prettyShow q)

-- | To process the target type.
typeEndsInDef :: MonadTCM tcm => Type -> tcm (Maybe QName)
typeEndsInDef t = liftTCM $ do
  TelV _ core <- telViewPath t
  case unEl core of
    Def d vs -> return $ Just d
    _        -> return Nothing

-- | Termination check a definition by pattern matching.
--
--   TODO: Refactor!
--   As this function may be called twice,
--   once disregarding dot patterns,
--   the second time regarding dot patterns,
--   it is better if we separated bare call extraction
--   from computing the change in structural order.
--   Only the latter depends on the choice whether we
--   consider dot patterns or not.
termDef :: QName -> TerM Calls
termDef name = terSetCurrent name $ inConcreteOrAbstractMode name $ \ def -> do

  -- Retrieve definition
  let t = defType def

  liftTCM $ reportSDoc "term.def.fun" 5 $
    sep [ "termination checking type of" <+> prettyTCM name
        , nest 2 $ ":" <+> prettyTCM t
        ]

  termType t `mappend` do

  liftTCM $ reportSDoc "term.def.fun" 5 $
    sep [ "termination checking body of" <+> prettyTCM name
        , nest 2 $ ":" <+> prettyTCM t
        ]

  -- If --without-K, we disregard all arguments (and result)
  -- which are not of data or record type.

  withoutKEnabled <- liftTCM withoutKOption
  applyWhen withoutKEnabled (setMasks t) $ do

    -- If the result should be disregarded, set all calls to unguarded.
    applyWhenM terGetMaskResult terUnguarded $ do

      case theDef def of
        Function{ funClauses = cls, funDelayed = delayed } ->
          terSetDelayed delayed $ forM' cls $ \ cl -> do
            if hasDefP (namedClausePats cl) -- generated hcomp clause, should be safe.
                                            -- TODO find proper strategy.
              then return empty
              else termClause cl

        _ -> return empty
  where
    hasDefP :: [NamedArg DeBruijnPattern] -> Bool
    hasDefP ps = getAny $ flip foldPattern ps $ \ (x :: DeBruijnPattern) ->
                  case x of
                    DefP{} -> Any True
                    _      -> Any False


-- | Collect calls in type signature @f : (x1:A1)...(xn:An) -> B@.
--   It is treated as if there were the additional function clauses.
--   @@
--      f = A1
--      f x1 = A2
--      f x1 x2 = A3
--      ...
--      f x1 ... xn = B
--   @@

termType :: Type -> TerM Calls
termType = return mempty
-- termType = loop 0  -- Andreas, 2019-04-10 deactivate for backwards-compatibility in 2.6.0 #1556
  where
  loop n t = do
    ps <- mkPats n
    reportSDoc "term.type" 60 $ vcat
      [ text $ "termType " ++ show n ++ " with " ++ show (length ps) ++ " patterns"
      , nest 2 $ "looking at type " <+> prettyTCM t
      ]
    tel <- getContextTelescope  -- Andreas, 2018-11-15, issue #3394, forgotten initialization of terSizeDepth
    terSetPatterns ps $ terSetSizeDepth tel $ do
      ifNotPiType t {-then-} extract {-else-} $ \ dom absB -> do
        extract dom `mappend` underAbstractionAbs dom absB (loop $! n + 1)

  -- create n variable patterns
  mkPats n  = zipWith mkPat (downFrom n) <$> getContextNames
  mkPat i x = notMasked $ VarP PatOSystem $ DBPatVar (prettyShow x) i

-- | Mask arguments and result for termination checking
--   according to type of function.
--   Only arguments of types ending in data/record or Size are counted in.
setMasks :: Type -> TerM a -> TerM a
setMasks t cont = do
  (ds, d) <- liftTCM $ do
    TelV tel core <- telViewPath t
    -- Check argument types
    ds <- forM (telToList tel) $ \ t -> do
      TelV _ t <- telViewPath $ snd $ unDom t
      d <- (isNothing <$> isDataOrRecord (unEl t)) `or2M` (isJust <$> isSizeType t)
      when d $
        reportSDoc "term.mask" 20 $ do
          "argument type "
            <+> prettyTCM t
            <+> " is not data or record type, ignoring structural descent for --without-K"
      return d
    -- Check result types
    d  <- isNothing <.> isDataOrRecord . unEl $ core
    when d $
      reportSLn "term.mask" 20 $ "result type is not data or record type, ignoring guardedness for --without-K"
    return (ds, d)
  terSetMaskArgs (ds ++ repeat True) $ terSetMaskResult d $ cont


-- | Is the current target type among the given ones?

targetElem :: [Target] -> TerM Bool
targetElem ds = maybe False (`elem` ds) <$> terGetTarget

{-
-- | The target type of the considered recursive definition.
data Target
  = Set        -- ^ Constructing a Set (only meaningful with 'guardingTypeConstructors').
  | Data QName -- ^ Constructing a coinductive or mixed type (could be data or record).
  deriving (Eq, Show)

-- | Check wether a 'Target" corresponds to the current one.
matchingTarget :: DBPConf -> Target -> TCM Bool
matchingTarget conf t = maybe (return True) (match t) (currentTarget conf)
  where
    match Set      Set       = return True
    match (Data d) (Data d') = mutuallyRecursive d d'
    match _ _                = return False
-}

-- | Convert a term (from a dot pattern) to a DeBruijn pattern.
--
--   The term is first normalized and stripped of all non-coinductive projections.

termToDBP :: Term -> TerM DeBruijnPattern
termToDBP t = ifNotM terGetUseDotPatterns (return unusedVar) $ {- else -} do
  termToPattern =<< do liftTCM $ stripAllProjections =<< normalise t

-- | Convert a term (from a dot pattern) to a pattern for the purposes of the termination checker.
--
--   @SIZESUC@ is treated as a constructor.

class TermToPattern a b where
  termToPattern :: a -> TerM b

  default termToPattern :: (TermToPattern a' b', Traversable f, a ~ f a', b ~ f b') => a -> TerM b
  termToPattern = traverse termToPattern

instance TermToPattern a b => TermToPattern [a] [b] where
instance TermToPattern a b => TermToPattern (Arg a) (Arg b) where
instance TermToPattern a b => TermToPattern (Named c a) (Named c b) where

-- OVERLAPPING
-- instance TermToPattern a b => TermToPattern a (Named c b) where
--   termToPattern t = unnamed <$> termToPattern t

instance TermToPattern Term DeBruijnPattern where
  termToPattern t = (liftTCM $ constructorForm t) >>= \case
    -- Constructors.
    Con c _ args -> ConP c noConPatternInfo . map (fmap unnamed) <$> termToPattern (fromMaybe __IMPOSSIBLE__ $ allApplyElims args)
    Def s [Apply arg] -> do
      suc <- terGetSizeSuc
      if Just s == suc then ConP (ConHead s Inductive []) noConPatternInfo . map (fmap unnamed) <$> termToPattern [arg]
       else return $ dotP t
    DontCare t  -> termToPattern t -- OR: __IMPOSSIBLE__  -- removed by stripAllProjections
    -- Leaves.
    Var i []    -> varP . (`DBPatVar` i) . prettyShow <$> nameOfBV i
    Lit l       -> return $ LitP l
    Dummy s _   -> __IMPOSSIBLE_VERBOSE__ s
    t           -> return $ dotP t


-- | Masks all non-data/record type patterns if --without-K.
--   See issue #1023.
maskNonDataArgs :: [DeBruijnPattern] -> TerM [Masked DeBruijnPattern]
maskNonDataArgs ps = zipWith mask ps <$> terGetMaskArgs
  where
    mask p@ProjP{} _ = Masked False p
    mask p         d = Masked d     p


-- | Extract recursive calls from one clause.

termClause :: Clause -> TerM Calls
termClause clause = do

  -- If with-function inlining is disallowed (e.g. --without-K),
  -- we check the original clause.

  let fallback = termClause' clause
  ifNotM (terGetInlineWithFunctions) fallback $ {- else -} do

    -- Otherwise, we will do inlining, hence, can skip with-generated functions.

    name <- terGetCurrent
    ifM (isJust <$> isWithFunction name) (return mempty) $ {- else -} do

      -- With inlining, the termination check for all subordinated
      -- with-functions is included in the parent function.

      (liftTCM $ inlineWithClauses name clause) >>= \case
        Nothing  -> fallback
        Just cls -> terSetHaveInlinedWith $ mapM' termClause' cls

termClause' :: Clause -> TerM Calls
termClause' clause = do
  Clause{ clauseTel = tel, namedClausePats = ps, clauseBody = body } <- etaExpandClause clause
  liftTCM $ reportSDoc "term.check.clause" 25 $ vcat
    [ "termClause"
    , nest 2 $ "tel =" <+> prettyTCM tel
    , nest 2 $ "ps  =" <+> do addContext tel $ prettyTCMPatternList ps
    ]
  forM' body $ \ v -> addContext tel $ do
    -- TODO: combine the following two traversals, avoid full normalisation.
    -- Parse dot patterns as patterns as far as possible.
    ps <- postTraversePatternM parseDotP ps
    -- Blank out coconstructors.
    ps <- preTraversePatternM stripCoCon ps
    -- Mask non-data arguments.
    mdbpats <- maskNonDataArgs $ map namedArg ps
    terSetPatterns mdbpats $ do
      terSetSizeDepth tel $ do
        reportBody v
        extract v

  where
    parseDotP = \case
      DotP o t -> termToDBP t
      p        -> return p
    stripCoCon p = case p of
      ConP (ConHead c _ _) _ _ -> do
        ifM ((Just c ==) <$> terGetSizeSuc) (return p) $ {- else -} do
        whatInduction c >>= \case
          Inductive   -> return p
          CoInductive -> return unusedVar
      _ -> return p
    reportBody :: Term -> TerM ()
    reportBody v = verboseS "term.check.clause" 6 $ do
      f       <- terGetCurrent
      delayed <- terGetDelayed
      pats    <- terGetPatterns
      liftTCM $ reportSDoc "term.check.clause" 6 $ do
        sep [ text ("termination checking " ++
                    (if delayed == Delayed then "delayed " else "") ++
                    "clause of")
                <+> prettyTCM f
            , nest 2 $ "lhs:" <+> sep (map prettyTCM pats)
            , nest 2 $ "rhs:" <+> prettyTCM v
            ]


-- | Extract recursive calls from expressions.
class ExtractCalls a where
  extract :: a -> TerM Calls

instance ExtractCalls a => ExtractCalls (Abs a) where
  extract (NoAbs _ a) = extract a
  extract (Abs x a)   = addContext x $ terRaise $ extract a

instance ExtractCalls a => ExtractCalls (Arg a) where
  extract = extract . unArg

instance ExtractCalls a => ExtractCalls (Dom a) where
  extract = extract . unDom

instance ExtractCalls a => ExtractCalls (Elim' a) where
  extract Proj{}    = return empty
  extract (Apply a) = extract $ unArg a
  extract (IApply x y a) = extract (x,(y,a)) -- TODO Andrea: conservative

instance ExtractCalls a => ExtractCalls [a] where
  extract = mapM' extract

instance (ExtractCalls a, ExtractCalls b) => ExtractCalls (a,b) where
  extract (a, b) = CallGraph.union <$> extract a <*> extract b

-- | Sorts can contain arbitrary terms of type @Level@,
--   so look for recursive calls also in sorts.
--   Ideally, 'Sort' would not be its own datatype but just
--   a subgrammar of 'Term', then we would not need this boilerplate.

instance ExtractCalls Sort where
  extract s = do
    liftTCM $ do
      reportSDoc "term.sort" 20 $
        "extracting calls from sort" <+> prettyTCM s
      reportSDoc "term.sort" 50 $
        text ("s = " ++ show s)
    case s of
      Inf        -> return empty
      SizeUniv   -> return empty
      Type t     -> terUnguarded $ extract t  -- no guarded levels
      Prop t     -> terUnguarded $ extract t
      PiSort s1 s2 -> extract (s1, s2)
      UnivSort s -> extract s
      MetaS x es -> return empty
      DefS d es  -> return empty
      DummyS{}   -> return empty

-- | Extract recursive calls from a type.

instance ExtractCalls Type where
  extract (El s t) = extract (s, t)

-- | Extract recursive calls from a constructor application.

constructor
  :: QName
    -- ^ Constructor name.
  -> Induction
    -- ^ Should the constructor be treated as inductive or coinductive?
  -> [(Arg Term, Bool)]
    -- ^ All the arguments,
    --   and for every argument a boolean which is 'True' iff the
    --   argument should be viewed as preserving guardedness.
  -> TerM Calls
constructor c ind args = do
  cutoff <- terGetCutOff
  let ?cutoff = cutoff
  forM' args $ \ (arg, preserves) -> do
    let g' = case (preserves, ind) of
             (True,  Inductive)   -> id
             (True,  CoInductive) -> (Order.lt .*.)
             (False, _)           -> const Order.unknown
    terModifyGuarded g' $ extract arg

-- | Extract calls from with function application.

withFunction :: QName -> Elims -> TerM Calls
withFunction g es = do
  v <- liftTCM $ -- billTo [Benchmark.Termination, Benchmark.With] $  -- 0ms
         expandWithFunctionCall g es
  liftTCM $ reportSDoc "term.with.call" 30 $
    "termination checking expanded with-function call:" <+> prettyTCM v
  extract v

-- | Handles function applications @g es@.

function :: QName -> Elims -> TerM Calls
function g es0 = ifM (terGetInlineWithFunctions `and2M` do isJust <$> isWithFunction g) (withFunction g es0)
  $ {-else, no with function-} do

    f       <- terGetCurrent
    names   <- terGetMutual
    guarded <- terGetGuarded

    -- let gArgs = Def g es0
    liftTCM $ reportSDoc "term.function" 30 $
      "termination checking function call " <+> prettyTCM (Def g es0)

    -- First, look for calls in the arguments of the call gArgs.

    -- We have to reduce constructors in case they're reexported.
    -- Andreas, Issue 1530: constructors have to be reduced deep inside terms,
    -- thus, we need to use traverseTermM.
    let (reduceCon :: Term -> TCM Term) = traverseTermM $ \ t -> case t of
           Con c ci vs -> (`applyE` vs) <$> reduce (Con c ci [])  -- make sure we don't reduce the arguments
           _ -> return t

    -- Reduce constructors only when this call is actually a recursive one.
    -- es <- liftTCM $ billTo [Benchmark.Termination, Benchmark.Reduce] $ forM es $
    --         etaContract <=< traverse reduceCon <=< instantiateFull

    -- If the function is a projection but not for a coinductive record,
    -- then preserve guardedness for its principal argument.
    isProj <- isProjectionButNotCoinductive g
    let unguards = repeat Order.unknown
    let guards = applyWhen isProj (guarded :) unguards
    -- Collect calls in the arguments of this call.
    let args = map unArg $ argsFromElims es0
    calls <- forM' (zip guards args) $ \ (guard, a) -> do
      terSetGuarded guard $ extract a

    -- Then, consider call gArgs itself.

    liftTCM $ reportSDoc "term.found.call" 20 $
      sep [ "found call from" <+> prettyTCM f
          , nest 2 $ "to" <+> prettyTCM g
          ]

    -- insert this call into the call list
    case List.elemIndex g names of

       -- call leads outside the mutual block and can be ignored
       Nothing   -> return calls

       -- call is to one of the mutally recursive functions
       Just gInd -> do
         delayed <- terGetDelayed
         -- Andreas, 2017-02-14, issue #2458:
         -- If we have inlined with-functions, we could be illtyped,
         -- hence, do not reduce anything.
         -- Andreas, 2017-06-20 issue #2613:
         -- We still need to reduce constructors, even when with-inlining happened.
         es <- -- ifM terGetHaveInlinedWith (return es0) {-else-} $
           liftTCM $ forM es0 $
             -- 2017-09-09, re issue #2732
             -- The eta-contraction here does not seem necessary to make structural order
             -- comparison not having to worry about eta.
             -- Maybe we thought an eta redex could come from a meta instantiation.
             -- However, eta-contraction is already performed by instantiateFull.
             -- See test/Succeed/Issue2732-termination.agda.
             -- etaContract <=<
             traverse reduceCon <=< instantiateFull

           -- 2017-05-16, issue #2403: Argument normalization is too expensive,
           -- even if we only expand non-recursive functions.
           -- Argument normalization TURNED OFF.
           -- liftTCM $ billTo [Benchmark.Termination, Benchmark.Reduce] $ do
           --  -- Andreas, 2017-01-13, issue #2403, normalize arguments for the structural ordering.
           --  -- Andreas, 2017-03-25, issue #2495, restrict this to non-recursive functions
           --  -- otherwise, the termination checking may run forever.
           --  reportSLn "term.reduce" 90 $ "normalizing call arguments"
           --  modifyAllowedReductions (List.\\ [UnconfirmedReductions,RecursiveReductions]) $
           --    forM es0 $ \ e -> do
           --      reportSDoc "term.reduce" 95 $ "normalizing " <+> prettyTCM e
           --      etaContract =<< normalise e

         -- Compute the call matrix.

         -- Andreas, 2014-03-26 only 6% of termination time for library test
         -- spent on call matrix generation
         (nrows, ncols, matrix) <- billTo [Benchmark.Termination, Benchmark.Compare] $
           compareArgs es
         -- only a delayed definition can be guarded
         let ifDelayed o | Order.decreasing o && delayed == NotDelayed = Order.le
                         | otherwise                                  = o
         liftTCM $ reportSLn "term.guardedness" 20 $
           "composing with guardedness " ++ prettyShow guarded ++
           " counting as " ++ prettyShow (ifDelayed guarded)
         cutoff <- terGetCutOff
         let ?cutoff = cutoff
         let matrix' = composeGuardedness (ifDelayed guarded) matrix

         -- Andreas, 2013-04-26 FORBIDDINGLY expensive!
         -- This PrettyTCM QName cost 50% of the termination time for std-lib!!
         -- gPretty <-liftTCM $ billTo [Benchmark.Termination, Benchmark.Level] $
         --   render <$> prettyTCM g

         -- Andreas, 2013-05-19 as pointed out by Andrea Vezzosi,
         -- printing the call eagerly is forbiddingly expensive.
         -- So we build a closure such that we can print the call
         -- whenever we really need to.
         -- This saves 30s (12%) on the std-lib!
         -- Andreas, 2015-01-21 Issue 1410: Go to the module where g is defined
         -- otherwise its free variables with be prepended to the call
         -- in the error message.
         doc <- liftTCM $ withCurrentModule (qnameModule g) $ buildClosure $
           Def g $ reverse $ dropWhile ((Inserted ==) . getOrigin) $ reverse es0
           -- Andreas, 2018-07-22, issue #3136
           -- Dropping only inserted arguments at the end, since
           -- dropping arguments in the middle might make the printer crash.
           -- Def g $ filter ((/= Inserted) . getOrigin) es0
           -- Andreas, 2017-01-05, issue #2376
           -- Remove arguments inserted by etaExpandClause.

         let src  = fromMaybe __IMPOSSIBLE__ $ List.elemIndex f names
             tgt  = gInd
             cm   = makeCM ncols nrows matrix'
             info = CallPath [CallInfo
                      { callInfoTarget = g
                      , callInfoRange  = getRange g
                      , callInfoCall   = doc
                      }]
         verboseS "term.kept.call" 5 $ do
           pats <- terGetPatterns
           reportSDoc "term.kept.call" 5 $ vcat
             [ "kept call from" <+> text (prettyShow f) <+> hsep (map prettyTCM pats)
             , nest 2 $ "to" <+> text (prettyShow g) <+>
                         hsep (map (parens . prettyTCM) args)
             , nest 2 $ "call matrix (with guardedness): "
             , nest 2 $ pretty cm
             ]
         return $ CallGraph.insert src tgt cm info calls

-- | Extract recursive calls from a term.

instance ExtractCalls Term where
  extract t = do
    liftTCM $ reportSDoc "term.check.term" 50 $ do
      "looking for calls in" <+> prettyTCM t

    -- Instantiate top-level MetaVar.
    t <- liftTCM $ instantiate t
    case t of

      -- Constructed value.
      Con ConHead{conName = c} _ es -> do
        let args = fromMaybe __IMPOSSIBLE__ $ allApplyElims es
        -- A constructor preserves the guardedness of all its arguments.
        let argsg = zip args $ repeat True

        -- If we encounter a coinductive record constructor
        -- in a type mutual with the current target
        -- then we count it as guarding.
        ind <- ifM ((Just c ==) <$> terGetSharp) (return CoInductive) $ do
          caseMaybeM (liftTCM $ isRecordConstructor c) (return Inductive) $ \ (q, def) -> do
            reportSLn "term.check.term" 50 $ "constructor " ++ prettyShow c ++ " has record type " ++ prettyShow q
            (\ b -> if b then CoInductive else Inductive) <$>
              andM [ return $ recInduction def == Just CoInductive
                   , targetElem . fromMaybe __IMPOSSIBLE__ $ recMutual def
                   ]
        constructor c ind argsg

      -- Function, data, or record type.
      Def g es -> function g es

      -- Abstraction. Preserves guardedness.
      Lam h b -> extract b

      -- Neutral term. Destroys guardedness.
      Var i es -> terUnguarded $ extract es

      -- Dependent function space. Destroys guardedness.
      Pi a (Abs x b) ->
        terUnguarded $
        CallGraph.union <$>
        extract a <*> do
          a <- maskSizeLt a  -- OR: just do not add a to the context!
          addContext (x, a) $ terRaise $ extract b

      -- Non-dependent function space. Destroys guardedness.
      Pi a (NoAbs _ b) ->
        terUnguarded $ CallGraph.union <$> extract a <*> extract b

      -- Literal.
      Lit l -> return empty

      -- Sort.
      Sort s -> extract s

      -- Unsolved metas are not considered termination problems, there
      -- will be a warning for them anyway.
      MetaV x args -> return empty

      -- Erased and not-yet-erased proof.
      DontCare t -> extract t

      -- Level.
      Level l -> -- billTo [Benchmark.Termination, Benchmark.Level] $ do
        -- Andreas, 2014-03-26 Benchmark discontinued, < 0.3% spent on levels.
        extract l

      -- Dummy.
      Dummy{} -> return empty

-- | Extract recursive calls from level expressions.

deriving instance ExtractCalls Level

instance ExtractCalls PlusLevel where
  extract (ClosedLevel n) = return $ mempty
  extract (Plus n l)      = extract l

instance ExtractCalls LevelAtom where
  extract (MetaLevel x es)   = extract es
  extract (BlockedLevel x t) = extract t
  extract (NeutralLevel _ t) = extract t
  extract (UnreducedLevel t) = extract t

-- | Rewrite type @tel -> Size< u@ to @tel -> Size@.
maskSizeLt :: MonadTCM tcm => Dom Type -> tcm (Dom Type)
maskSizeLt !dom = liftTCM $ do
  let a = unDom dom
  (msize, msizelt) <- getBuiltinSize
  case (msize, msizelt) of
    (_ , Nothing) -> return dom
    (Nothing, _)  -> __IMPOSSIBLE__
    (Just size, Just sizelt) -> do
      TelV tel c <- telView a
      case a of
        El s (Def d [v]) | d == sizelt -> return $
          (abstract tel $ El s $ Def size []) <$ dom
        _ -> return dom

{- | @compareArgs es@

     Compare the list of de Bruijn patterns (=parameters) @pats@
     with a list of arguments @es@ and create a call maxtrix
     with |es| rows and |pats| columns.

     The guardedness is the number of projection patterns in @pats@
     minus the number of projections in @es@.
 -}
compareArgs :: [Elim] -> TerM (Int, Int, [[Order]])
compareArgs es = do
  pats <- terGetPatterns
  liftTCM $ reportSDoc "term.compareArgs" 90 $ vcat
    [ text $ "comparing " ++ show (length es) ++ " args to " ++ show (length pats) ++ " patterns"
    ]
  -- apats <- annotatePatsWithUseSizeLt pats
  -- reportSDoc "term.compare" 20 $
  --   "annotated patterns = " <+> sep (map prettyTCM apats)
  -- matrix <- forM es $ \ e -> forM apats $ \ (b, p) -> terSetUseSizeLt b $ compareElim e p
  matrix <- withUsableVars pats $ forM es $ \ e -> forM pats $ \ p -> compareElim e p

  -- Count the number of coinductive projection(pattern)s in caller and callee.
  -- Only recursive coinductive projections are eligible (Issue 1209).
  projsCaller <- length <$> do
    filterM (isCoinductiveProjection True) $ mapMaybe (fmap (headAmbQ . snd) . isProjP . getMasked) pats
  projsCallee <- length <$> do
    filterM (isCoinductiveProjection True) $ mapMaybe (fmap snd . isProjElim) es
  cutoff <- terGetCutOff
  let ?cutoff = cutoff
  useGuardedness <- liftTCM guardednessOption
  let guardedness =
        if useGuardedness
        then decr True $ projsCaller - projsCallee
        else Order.Unknown
  liftTCM $ reportSDoc "term.guardedness" 30 $ sep
    [ "compareArgs:"
    , nest 2 $ text $ "projsCaller = " ++ prettyShow projsCaller
    , nest 2 $ text $ "projsCallee = " ++ prettyShow projsCallee
    , nest 2 $ text $ "guardedness of call: " ++ prettyShow guardedness
    ]
  return $ addGuardedness guardedness (size es, size pats, matrix)

-- | Traverse patterns from left to right.
--   When we come to a projection pattern,
--   switch usage of SIZELT constraints:
--   on, if coinductive,
--   off, if inductive.
--
--   UNUSED
annotatePatsWithUseSizeLt :: [DeBruijnPattern] -> TerM [(Bool,DeBruijnPattern)]
annotatePatsWithUseSizeLt = loop where
  loop [] = return []
  loop (p@(ProjP _ q) : pats) = ((False,p) :) <$> do projUseSizeLt q $ loop pats
  loop (p : pats) = (\ b ps -> (b,p) : ps) <$> terGetUseSizeLt <*> loop pats


-- | @compareElim e dbpat@

compareElim :: Elim -> Masked DeBruijnPattern -> TerM Order
compareElim e p = do
  liftTCM $ do
    reportSDoc "term.compare" 30 $ sep
      [ "compareElim"
      , nest 2 $ "e = " <> prettyTCM e
      , nest 2 $ "p = " <> prettyTCM p
      ]
    reportSDoc "term.compare" 50 $ sep
      [ nest 2 $ text $ "e = " ++ show e
      , nest 2 $ text $ "p = " ++ show p
      ]
  case (e, getMasked p) of
    (Proj _ d, ProjP _ d') -> do
      d  <- getOriginalProjection d
      d' <- getOriginalProjection d'
      o  <- compareProj d d'
      reportSDoc "term.compare" 30 $ sep
        [ text $ "comparing callee projection " ++ prettyShow d
        , text $ "against caller projection " ++ prettyShow d'
        , text $ "yields order " ++ prettyShow o
        ]
      return o
    (Proj{}, _)            -> return Order.unknown
    (Apply{}, ProjP{})     -> return Order.unknown
    (Apply arg, _)         -> compareTerm (unArg arg) p
    -- TODO Andrea: making sense?
    (IApply{}, ProjP{})  -> return Order.unknown
    (IApply _ _ arg, _)    -> compareTerm arg p

-- | In dependent records, the types of later fields may depend on the
--   values of earlier fields.  Thus when defining an inhabitant of a
--   dependent record type such as Σ by copattern matching,
--   a recursive call eliminated by an earlier projection (proj₁) might
--   occur in the definition at a later projection (proj₂).
--   Thus, earlier projections are considered "smaller" when
--   comparing copattern spines.  This is an ok approximation
--   of the actual dependency order.
--   See issues 906, 942.
compareProj :: MonadTCM tcm => QName -> QName -> tcm Order
compareProj d d'
  | d == d' = return Order.le
  | otherwise = liftTCM $ do
      -- different projections
      mr  <- getRecordOfField d
      mr' <- getRecordOfField d'
      case (mr, mr') of
        (Just r, Just r') | r == r' -> do
          -- of same record
          def <- theDef <$> getConstInfo r
          case def of
            Record{ recFields = fs } -> do
              fs <- return $ map unArg fs
              case (List.find (d==) fs, List.find (d'==) fs) of
                (Just i, Just i')
                  -- earlier field is smaller
                  | i < i'    -> return Order.lt
                  | i == i'   -> do
                     __IMPOSSIBLE__
                  | otherwise -> return Order.unknown
                _ -> __IMPOSSIBLE__
            _ -> __IMPOSSIBLE__
        _ -> return Order.unknown

-- | 'makeCM' turns the result of 'compareArgs' into a proper call matrix
makeCM :: Int -> Int -> [[Order]] -> CallMatrix
makeCM ncols nrows matrix = CallMatrix $
  Matrix.fromLists (Matrix.Size nrows ncols) matrix

-- | 'addGuardedness' adds guardedness flag in the upper left corner
-- (0,0).
addGuardedness :: Order -> (Int, Int, [[Order]]) -> (Int, Int, [[Order]])
addGuardedness o (nrows, ncols, m) =
  (nrows + 1, ncols + 1,
   (o : replicate ncols Order.unknown) : map (Order.unknown :) m)

-- | Compose something with the upper-left corner of a call matrix
composeGuardedness :: (?cutoff :: CutOff) => Order -> [[Order]] -> [[Order]]
composeGuardedness o ((corner : row) : rows) = ((o .*. corner) : row) : rows
composeGuardedness _ _ = __IMPOSSIBLE__

-- | Stripping off a record constructor is not counted as decrease, in
--   contrast to a data constructor.
--   A record constructor increases/decreases by 0, a data constructor by 1.
offsetFromConstructor :: MonadTCM tcm => QName -> tcm Int
offsetFromConstructor c = maybe 1 (const 0) <$> do
  liftTCM $ isRecordConstructor c

-- | Compute the proper subpatterns of a 'DeBruijnPattern'.
subPatterns :: DeBruijnPattern -> [DeBruijnPattern]
subPatterns = foldPattern $ \case
  ConP _ _ ps -> map namedArg ps
  DefP _ _ ps -> map namedArg ps -- TODO check semantics
  VarP _ _    -> mempty
  LitP _      -> mempty
  DotP _ _    -> mempty
  ProjP _ _   -> mempty
  IApplyP{}   -> mempty


compareTerm :: Term -> Masked DeBruijnPattern -> TerM Order
compareTerm t p = do
--   reportSDoc "term.compare" 25 $
--     " comparing term " <+> prettyTCM t <+>
--     " to pattern " <+> prettyTCM p
  t <- liftTCM $ stripAllProjections t
  o <- compareTerm' t p
  liftTCM $ reportSDoc "term.compare" 25 $
    " comparing term " <+> prettyTCM t <+>
    " to pattern " <+> prettyTCM p <+>
    text (" results in " ++ prettyShow o)
  return o


-- | Remove all non-coinductive projections from an algebraic term
--   (not going under binders).
--   Also, remove 'DontCare's.
--
class StripAllProjections a where
  stripAllProjections :: a -> TCM a

instance StripAllProjections a => StripAllProjections (Arg a) where
  stripAllProjections = traverse stripAllProjections

instance StripAllProjections Elims where
  stripAllProjections es =
    case es of
      []             -> return []
      (Apply a : es) -> do
        (:) <$> (Apply <$> stripAllProjections a) <*> stripAllProjections es
      (IApply x y a : es) -> do
        -- TODO Andrea: are we doind extra work?
        (:) <$> (IApply <$> stripAllProjections x
                        <*> stripAllProjections y
                        <*> stripAllProjections a)
            <*> stripAllProjections es
      (Proj o p  : es) -> do
        isP <- isProjectionButNotCoinductive p
        applyUnless isP (Proj o p :) <$> stripAllProjections es

instance StripAllProjections Args where
  stripAllProjections = mapM stripAllProjections

instance StripAllProjections Term where
  stripAllProjections t = do
    case t of
      Var i es   -> Var i <$> stripAllProjections es
      Con c ci ts -> do
        -- Andreas, 2019-02-23, re #2613.  This is apparently not necessary:
        -- c <- fromRightM (\ err -> return c) $ getConForm (conName c)
        Con c ci <$> stripAllProjections ts
      Def d es   -> Def d <$> stripAllProjections es
      DontCare t -> stripAllProjections t
      _ -> return t

-- | Normalize outermost constructor name in a pattern.

reduceConPattern :: DeBruijnPattern -> TCM DeBruijnPattern
reduceConPattern = \case
  ConP c i ps -> fromRightM (\ err -> return c) (getConForm (conName c)) <&> \ c' ->
    ConP c' i ps
  p -> return p

-- | @compareTerm' t dbpat@

compareTerm' :: Term -> Masked DeBruijnPattern -> TerM Order
compareTerm' v mp@(Masked m p) = do
  suc  <- terGetSizeSuc
  cutoff <- terGetCutOff
  let ?cutoff = cutoff
  v <- liftTCM (instantiate v)
  p <- liftTCM $ reduceConPattern p
  case (v, p) of

    -- Andreas, 2013-11-20 do not drop projections,
    -- in any case not coinductive ones!:
    (Var i es, _) | Just{} <- allApplyElims es ->
      compareVar i mp

    (DontCare t, _) ->
      compareTerm' t mp

    -- Andreas, 2014-09-22, issue 1281:
    -- For metas, termination checking should be optimistic.
    -- If there is any instance of the meta making termination
    -- checking succeed, then we should not fail.
    -- Thus, we assume the meta will be instantiated with the
    -- deepest variable in @p@.
    -- For sized types, the depth is maximally
    -- the number of SIZELT hypotheses one can have in a context.
    (MetaV{}, p) -> Order.decr True . max (if m then 0 else patternDepth p) . pred <$>
       terAsks _terSizeDepth

    -- Successor on both sides cancel each other.
    -- We ignore the mask for sizes.
    (Def s [Apply t], ConP s' _ [p]) | s == conName s' && Just s == suc ->
      compareTerm' (unArg t) (notMasked $ namedArg p)

    -- Register also size increase.
    (Def s [Apply t], p) | Just s == suc ->
      -- Andreas, 2012-10-19 do not cut off here
      increase 1 <$> compareTerm' (unArg t) mp

    -- In all cases that do not concern sizes,
    -- we cannot continue if pattern is masked.

    _ | m -> return Order.unknown

    (Lit l, LitP l')
      | l == l'     -> return Order.le
      | otherwise   -> return Order.unknown

    (Lit l, _) -> do
      v <- liftTCM $ constructorForm v
      case v of
        Lit{}       -> return Order.unknown
        v           -> compareTerm' v mp

    -- Andreas, 2011-04-19 give subterm priority over matrix order

    (Con{}, ConP c _ ps) | any (isSubTerm v . namedArg) ps ->
      decr True <$> offsetFromConstructor (conName c)

    (Con c _ es, ConP c' _ ps) | conName c == conName c'->
      let ts = fromMaybe __IMPOSSIBLE__ $ allApplyElims es in
      compareConArgs ts ps

    (Con _ _ [], _) -> return Order.le

    -- new case for counting constructors / projections
    -- register also increase
    (Con c _ es, _) -> do
      let ts = fromMaybe __IMPOSSIBLE__ $ allApplyElims es
      increase <$> offsetFromConstructor (conName c)
               <*> (infimum <$> mapM (\ t -> compareTerm' (unArg t) mp) ts)

    (t, p) -> return $ subTerm t p

-- | @subTerm@ computes a size difference (Order)
subTerm :: (?cutoff :: CutOff) => Term -> DeBruijnPattern -> Order
subTerm t p = if equal t p then Order.le else properSubTerm t p
  where
    equal (Con c _ es) (ConP c' _ ps) =
      let ts = fromMaybe __IMPOSSIBLE__ $ allApplyElims es in
      and $ (conName c == conName c')
          : (length ts == length ps)
          : zipWith (\ t p -> equal (unArg t) (namedArg p)) ts ps
    equal (Var i []) (VarP _ x) = i == dbPatVarIndex x
    equal (Lit l)    (LitP l') = l == l'
    -- Terms.
    -- Checking for identity here is very fragile.
    -- However, we cannot do much more, as we are not allowed to normalize t.
    -- (It might diverge, and we are just in the process of termination checking.)
    equal t         (DotP _ t') = t == t'
    equal _ _ = False

    properSubTerm t (ConP _ _ ps) =
      setUsability True $ decrease 1 $ supremum $ map (subTerm t . namedArg) ps
    properSubTerm _ _ = Order.unknown

isSubTerm :: (?cutoff :: CutOff) => Term -> DeBruijnPattern -> Bool
isSubTerm t p = nonIncreasing $ subTerm t p

compareConArgs :: Args -> [NamedArg DeBruijnPattern] -> TerM Order
compareConArgs ts ps = do
  cutoff <- terGetCutOff
  let ?cutoff = cutoff
  -- we may assume |ps| >= |ts|, otherwise c ps would be of functional type
  -- which is impossible
  case (length ts, length ps) of
    (0,0) -> return Order.le        -- c <= c
    (0,1) -> return Order.unknown   -- c not<= c x
    (1,0) -> __IMPOSSIBLE__
    (1,1) -> compareTerm' (unArg (head ts)) (notMasked $ namedArg $ head ps)
    (_,_) -> foldl (Order..*.) Order.le <$>
               zipWithM compareTerm' (map unArg ts) (map (notMasked . namedArg) ps)
       -- corresponds to taking the size, not the height
       -- allows examples like (x, y) < (Succ x, y)
{- version which does an "order matrix"
   -- Andreas, 2013-02-18 disabled because it is unclear
   -- how to scale idempotency test to matrix-shaped orders (need thinking/researcH)
   -- Trigges issue 787.
        (_,_) -> do -- build "call matrix"
          m <- mapM (\t -> mapM (compareTerm' suc (unArg t)) ps) ts
          let m2 = makeCM (length ps) (length ts) m
          return $ Order.orderMat (Order.mat m2)
-}
{- version which takes height
--    if null ts then Order.Le
--               else Order.infimum (zipWith compareTerm' (map unArg ts) ps)
-}

compareVar :: Nat -> Masked DeBruijnPattern -> TerM Order
compareVar i (Masked m p) = do
  suc    <- terGetSizeSuc
  cutoff <- terGetCutOff
  let ?cutoff = cutoff
  let no = return Order.unknown
  case p of
    ProjP{}   -> no
    IApplyP _ _ _ x  -> compareVarVar i (Masked m x)
    LitP{}    -> no
    DotP{}   -> no
    VarP _ x  -> compareVarVar i (Masked m x)

    ConP s _ [p] | Just (conName s) == suc ->
      setUsability True . decrease 1 <$> compareVar i (notMasked $ namedArg p)

    ConP c _ ps -> if m then no else setUsability True <$> do
      decrease <$> offsetFromConstructor (conName c)
               <*> (Order.supremum <$> mapM (compareVar i . notMasked . namedArg) ps)
    DefP _ c ps -> if m then no else setUsability True <$> do
      decrease <$> offsetFromConstructor c
               <*> (Order.supremum <$> mapM (compareVar i . notMasked . namedArg) ps)
      -- This should be fine for c == hcomp

-- | Compare two variables.
--
--   The first variable comes from a term, the second from a pattern.
compareVarVar :: Nat -> Masked DBPatVar -> TerM Order
compareVarVar i (Masked m x@(DBPatVar _ j))
  | i == j = if not m then return Order.le else liftTCM $
      -- If j is a size, we ignore the mask.
      ifM (isJust <$> do isSizeType =<< reduce =<< typeOfBV j)
        {- then -} (return Order.le)
        {- else -} (return Order.unknown)
  | otherwise = do
      -- record usability of variable
      u <- (i `VarSet.member`) <$> terGetUsableVars
      -- Andreas, 2017-07-26, issue #2331.
      -- The usability logic is refuted by bounded size quantification in terms.
      -- Thus, it is switched off (the infrastructure remains in place for now).
      if not u then return Order.unknown else do
      -- Only if usable:
      res <- isBounded i
      case res of
        BoundedNo  -> return Order.unknown
        BoundedLt v -> setUsability u . decrease 1 <$> compareTerm' v (Masked m $ varP x)
