{-# LANGUAGE CPP #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeSynonymInstances #-}

{- Checking for Structural recursion
   Authors: Andreas Abel, Nils Anders Danielsson, Ulf Norell,
              Karl Mehltretter and others
   Created: 2007-05-28
   Source : TypeCheck.Rules.Decl
 -}

module Agda.Termination.TermCheck
    ( termDecl
    , Result, DeBruijnPat
    ) where

import Control.Applicative
import Control.Monad.Error
import Control.Monad.State

import Data.List as List
import Data.Maybe (mapMaybe, isJust, fromMaybe)
import Data.Monoid
import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.Traversable (traverse)

import Agda.Syntax.Abstract (IsProjP(..))
import qualified Agda.Syntax.Abstract as A
import Agda.Syntax.Internal as I
import qualified Agda.Syntax.Info as Info
import Agda.Syntax.Position
import Agda.Syntax.Common as Common
import Agda.Syntax.Literal (Literal(LitString))

import Agda.Termination.CutOff
import Agda.Termination.Monad
import Agda.Termination.CallGraph (CallGraph)
import Agda.Termination.CallGraph as CallGraph
import Agda.Termination.CallMatrix hiding (null)
import Agda.Termination.Order     as Order
import qualified Agda.Termination.SparseMatrix as Matrix
import Agda.Termination.Termination (endos, idempotent)
import qualified Agda.Termination.Termination  as Term
import Agda.Termination.RecCheck
import Agda.Termination.Inlining

import Agda.TypeChecking.Monad
import Agda.TypeChecking.Pretty
import Agda.TypeChecking.Reduce (reduce, normalise, instantiate, instantiateFull)
import Agda.TypeChecking.Records -- (isRecordConstructor, isInductiveRecord)
import Agda.TypeChecking.Telescope
import Agda.TypeChecking.EtaContract
import Agda.TypeChecking.Monad.Builtin
import Agda.TypeChecking.Substitute
import Agda.TypeChecking.SizedTypes
import Agda.TypeChecking.Datatypes

import qualified Agda.TypeChecking.Monad.Base.Benchmark as Benchmark
import Agda.TypeChecking.Monad.Benchmark (billTo, billPureTo)

import Agda.Interaction.Options

import Agda.Utils.Either
import Agda.Utils.Function
import Agda.Utils.Functor (($>), (<.>))
import Agda.Utils.List
import Agda.Utils.Size
import Agda.Utils.Maybe
import Agda.Utils.Monad -- (mapM', forM', ifM, or2M, and2M)
import Agda.Utils.Permutation
import Agda.Utils.Pointed
import Agda.Utils.Pretty (render)
import Agda.Utils.VarSet (VarSet)
import qualified Agda.Utils.VarSet as VarSet

#include "../undefined.h"
import Agda.Utils.Impossible

-- | Call graph with call info for composed calls.

type Calls = CallGraph CallPath

-- | The result of termination checking a module.
--   Must be 'Pointed' and a 'Monoid'.

type Result = [TerminationError]


-- | Termination check a single declaration.

termDecl :: A.Declaration -> TCM Result
termDecl d = ignoreAbstractMode $ termDecl' d


-- | Termination check a sequence of declarations.

termDecls :: [A.Declaration] -> TCM Result
termDecls ds = concat <$> mapM termDecl' ds


-- | Termination check a single declaration
--   (without necessarily ignoring @abstract@).

termDecl' :: A.Declaration -> TCM Result
termDecl' (A.ScopedDecl scope ds) = do
  setScope scope
  termDecls ds
termDecl' d = case d of
    A.Axiom {}            -> return mempty
    A.Field {}            -> return mempty
    A.Primitive {}        -> return mempty
    A.Mutual _ ds
      | [A.RecSig{}, A.RecDef _ r _ _ _ _ rds] <- unscopeDefs ds
                          -> checkRecDef ds r rds
    A.Mutual i ds         -> termMutual i ds
    A.Section _ x _ ds    -> termSection x ds
    A.Apply {}            -> return mempty
    A.Import {}           -> return mempty
    A.Pragma {}           -> return mempty
    A.Open {}             -> return mempty
    A.PatternSynDef {}    -> return mempty
        -- open and pattern synonym defs are just artifacts from the concrete syntax
    A.ScopedDecl{}        -> __IMPOSSIBLE__
        -- taken care of above
    A.RecSig{}            -> return mempty
    A.RecDef _ r _ _ _ _ ds -> checkRecDef [] r ds
    -- These should all be wrapped in mutual blocks
    A.FunDef{}  -> __IMPOSSIBLE__
    A.DataSig{} -> __IMPOSSIBLE__
    A.DataDef{} -> __IMPOSSIBLE__
    -- This should have been expanded to a proper declaration before termination checking
    A.UnquoteDecl{} -> __IMPOSSIBLE__
  where
    setScopeFromDefs = mapM_ setScopeFromDef
    setScopeFromDef (A.ScopedDecl scope d) = setScope scope
    setScopeFromDef _ = return ()

    unscopeDefs = concatMap unscopeDef

    unscopeDef (A.ScopedDecl _ ds) = unscopeDefs ds
    unscopeDef d = [d]

    checkRecDef ds r rds = do
      setScopeFromDefs ds
      termSection (mnameFromList $ qnameToList r) rds


-- | Termination check a module.

termSection :: ModuleName -> [A.Declaration] -> TCM Result
termSection x ds = do
  tel <- lookupSection x
  reportSDoc "term.section" 10 $
    sep [ text "termination checking section"
          , prettyTCM x
          , prettyTCM tel
          ]
  withCurrentModule x $ addCtxTel tel $ termDecls ds


-- | Termination check a bunch of mutually inductive recursive definitions.

termMutual :: Info.MutualInfo -> [A.Declaration] -> TCM Result
termMutual i ds = if names == [] then return mempty else

  -- We set the range to avoid panics when printing error messages.
  traceCall (SetRange (Info.mutualRange i)) $ do

  -- Get set of mutually defined names from the TCM.
  -- This includes local and auxiliary functions introduced
  -- during type-checking.
  mutualBlock <- findMutualBlock (head names)
  let allNames = Set.elems mutualBlock
      -- Andreas, 2014-03-26
      -- Keeping recursion check after experiments on the standard lib.
      -- Seems still to save 1s.
      -- skip = return False
      -- No need to term-check if the declarations are acyclic!
      skip = not <$> do
        billTo [Benchmark.Termination, Benchmark.RecCheck] $ recursive allNames

  -- NO_TERMINATION_CHECK
  if (Info.mutualTermCheck i == NoTerminationCheck) then do
      reportSLn "term.warn.yes" 2 $ "Skipping termination check for " ++ show names
      forM_ allNames $ \ q -> setTerminates q True -- considered terminating!
      return mempty
  -- NON_TERMINATING
    else if (Info.mutualTermCheck i == NonTerminating) then do
      reportSLn "term.warn.yes" 2 $ "Considering as non-terminating: " ++ show names
      forM_ allNames $ \ q -> setTerminates q False
      return mempty
  -- Trivially terminating (non-recursive)
    else ifM skip (do
      reportSLn "term.warn.yes" 2 $ "Trivially terminating: " ++ show names
      forM_ allNames $ \ q -> setTerminates q True
      return mempty)
   $ {- else -} do

     -- Assemble then initial configuration of the termination environment.

     cutoff <- optTerminationDepth <$> pragmaOptions

     reportSLn "term.top" 10 $ "Termination checking " ++ show names ++
       " with cutoff=" ++ show cutoff ++ "..."

     -- Get the name of size suc (if sized types are enabled)
     suc <- sizeSucName

     -- The name of sharp (if available).
     sharp <- fmap nameOfSharp <$> coinductionKit

     guardingTypeConstructors <-
       optGuardingTypeConstructors <$> pragmaOptions

     -- Andreas, 2014-08-28
     -- We do not inline with functions if --without-K.
     inlineWithFunctions <- not . optWithoutK <$> pragmaOptions

     let tenv = defaultTerEnv
           { terGuardingTypeConstructors = guardingTypeConstructors
           , terInlineWithFunctions      = inlineWithFunctions
           , terSizeSuc                  = suc
           , terSharp                    = sharp
           , terCutOff                   = cutoff
           , terMutual                   = allNames
           , terUserNames                = names
           }

     -- New check currently only makes a difference for copatterns.
     -- Since it is slow, only invoke it if --copatterns.
     res <- ifM (optCopatterns <$> pragmaOptions)
         -- Then: New check, one after another.
         (runTerm tenv $ forM' allNames $ termFunction)
         -- Else: Old check, all at once.
         (runTerm tenv $ termMutual')

     -- record result of termination check in signature
     let terminates = List.null res
     forM_ allNames $ \ q -> setTerminates q terminates
     return res

  where
    getName (A.FunDef i x delayed cs) = [x]
    getName (A.RecDef _ _ _ _ _ _ ds) = concatMap getName ds
    getName (A.Mutual _ ds)       = concatMap getName ds
    getName (A.Section _ _ _ ds)  = concatMap getName ds
    getName (A.ScopedDecl _ ds)   = concatMap getName ds
    getName _                     = []

    -- the mutual names mentioned in the abstract syntax
    names = concatMap getName ds


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
    Left calls -> do
      return $ point $ TerminationError
                { termErrFunctions = names
                , termErrCalls     = callInfos calls
                }
    Right{} -> do
      liftTCM $ reportSLn "term.warn.yes" 2 $
        show (names) ++ " does termination check"
      return mempty

billToTerGraph = billPureTo [Benchmark.Termination, Benchmark.Graph]

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
     [ "Calls (" ++ no ++ "dot patterns): " ++ show calls
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
           return (not $ CallGraph.null new, cs')
     report " Initial call matrices " cs0
     void $ trampolineM step cs0

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
     , nest 2 $ vcat $ punctuate (text "\n") $ map pretty idems
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

   -- Collect all recursive calls in the block,
   -- taking the target of the current function into account.

   let collect = forM' allNames termDef

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
     Left calls -> do
       return $ point $ TerminationError
         { termErrFunctions = if name `elem` names then [name] else []
         , termErrCalls     = calls
         }
     Right () -> do
       liftTCM $ reportSLn "term.warn.yes" 2 $
         show (name) ++ " does termination check"
       return mempty
  where
    reportTarget r = liftTCM $
      reportSLn "term.target" 20 $ "  target type " ++
        caseMaybe r "not recognized" (\ q ->
          "ends in " ++ show q)

-- | To process the target type.
typeEndsInDef :: MonadTCM tcm => Type -> tcm (Maybe QName)
typeEndsInDef t = liftTCM $ do
  TelV _ core <- telView t
  case ignoreSharing $ unEl core of
    Def d vs -> return $ Just d
    _        -> return Nothing

-- | Termination check a definition by pattern matching.
termDef :: QName -> TerM Calls
termDef name = terSetCurrent name $ do

  -- Retrieve definition
  def <- liftTCM $ getConstInfo name
  let t = defType def

  liftTCM $ reportSDoc "term.def.fun" 5 $
    sep [ text "termination checking body of" <+> prettyTCM name
        , nest 2 $ text ":" <+> prettyTCM t
        ]

  -- If --without-K, we disregard all arguments (and result)
  -- which are not of data or record type.

  withoutKEnabled <- liftTCM $ optWithoutK <$> pragmaOptions
  applyWhen withoutKEnabled (setMasks t) $ do

  -- If the result should be disregarded, set all calls to unguarded.
  applyUnlessM terGetMaskResult terUnguarded $ do

  case theDef def of
    Function{ funClauses = cls, funDelayed = delayed } ->
      terSetDelayed delayed $ forM' cls $ termClause

    _ -> return CallGraph.empty

-- | Mask arguments and result for termination checking
--   according to type of function.
--   Only arguments of data/record type are counted in.
setMasks :: Type -> TerM a -> TerM a
setMasks t cont = do
  (ds, d) <- liftTCM $ do
    TelV tel core <- telView t
    ds <- mapM ((isJust <.> isDataOrRecord) <=< (reduce . unEl . snd . unDom)) $ telToList tel
    d  <- isJust <.> isDataOrRecord . unEl $ core
    reportSLn "term.mask" 20 $ "result type is not data or record type, ignoring guardedness for --without-K"
    return (ds, d)
  terSetMaskArgs (ds ++ repeat False) $ terSetMaskResult d $ cont

{- Termination check clauses:

   For instance

   f x (cons y nil) = g x y

   Clause
     [VarP "x", ConP "List.cons" [VarP "y", ConP "List.nil" []]]
     Bind (Abs { absName = "x"
               , absBody = Bind (Abs { absName = "y"
                                     , absBody = Def "g" [ Var 1 []
                                                         , Var 0 []]})})

   Outline:
   - create "De Bruijn pattern"
   - collect recursive calls
   - going under a binder, lift de Bruijn pattern
   - compare arguments of recursive call to pattern

-}

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

termToDBP :: Term -> TerM DeBruijnPat
termToDBP t = ifNotM terGetUseDotPatterns (return unusedVar) $ {- else -} do
  suc <- terGetSizeSuc
  t <- liftTCM $ stripAllProjections =<< constructorForm t
  case ignoreSharing t of
    Var i []    -> return $ VarDBP i
    Con c args  -> ConDBP (conName c) <$> mapM (termToDBP . unArg) args
    Def s [Apply arg] | Just s == suc
                -> ConDBP s . (:[]) <$> termToDBP (unArg arg)
    Lit l       -> return $ LitDBP l
    _           -> return unusedVar


-- | Masks coconstructor patterns in a deBruijn pattern.
stripCoConstructors :: DeBruijnPat -> TerM DeBruijnPat
stripCoConstructors p = do
  case p of
    ConDBP c args -> do
      ind <- ifM ((Just c ==) <$> terGetSizeSuc) (return Inductive) {- else -}
               (liftTCM $ whatInduction c)
      case ind of
        Inductive   -> ConDBP c <$> mapM stripCoConstructors args
        CoInductive -> return unusedVar
    -- The remaining (atomic) patterns cannot contain coconstructors, obviously.
    VarDBP{}  -> return p
    LitDBP{}  -> return p
    ProjDBP{} -> return p

-- | Masks all non-data/record type patterns if --without-K.
maskNonDataArgs :: [DeBruijnPat] -> TerM [DeBruijnPat]
maskNonDataArgs ps = do
  zipWith (\ p d -> if d then p else unusedVar) ps <$> terGetMaskArgs

-- | cf. 'TypeChecking.Coverage.Match.buildMPatterns'
openClause :: Permutation -> [Pattern] -> ClauseBody -> TerM ([DeBruijnPat], Maybe Term)
openClause perm ps body = do
  -- invariant: xs has enough variables for the body
  unless (permRange perm == genericLength xs) __IMPOSSIBLE__
  dbps <- evalStateT (mapM build ps) xs
  return . (dbps,) $ case body `apply` map (defaultArg . var) xs of
    NoBody -> Nothing
    Body v -> Just v
    _      -> __IMPOSSIBLE__
  where
    -- length of the telescope
    n    = size perm
    -- the variables as a map from the body variables to the clause telescope
    xs   = permute (invertP perm) $ downFrom (size perm)

    tick = do x : xs <- get; put xs; return x

    build :: Pattern -> StateT [Nat] TerM DeBruijnPat
    build (VarP _)        = VarDBP <$> tick
    build (ConP con _ ps) = ConDBP (conName con) <$> mapM (build . namedArg) ps
    build (DotP t)        = tick *> do lift $ termToDBP t
    build (LitP l)        = return $ LitDBP l
    build (ProjP d)       = return $ ProjDBP d

-- | Extract recursive calls from one clause.
termClause :: Clause -> TerM Calls
termClause clause = do
  ifNotM (terGetInlineWithFunctions) (termClause' clause) $ {- else -} do
      name <- terGetCurrent
      ifM (isJust <$> do isWithFunction name) (return mempty) $ do
      mapM' termClause' =<< do liftTCM $ inlineWithClauses name clause

termClause' :: Clause -> TerM Calls
termClause' clause = do
  cl @ Clause { clauseTel  = tel
              , clausePerm = perm
              , clauseBody = body } <- introHiddenLambdas clause
  let argPats' = clausePats cl
  liftTCM $ reportSDoc "term.check.clause" 25 $ vcat
    [ text "termClause"
    , nest 2 $ text "tel      =" <+> prettyTCM tel
    , nest 2 $ text ("perm     = " ++ show perm)
    -- how to get the following right?
    -- , nest 2 $ text "argPats' =" <+> do prettyA =<< reifyPatterns tel perm argPats'
    ]
  addCtxTel tel $ do
    ps <- liftTCM $ normalise $ map unArg argPats'
    (dbpats, res) <- openClause perm ps body
    case res of
      Nothing -> return CallGraph.empty
      Just v -> do
        dbpats <- mapM stripCoConstructors dbpats
        dbpats <- maskNonDataArgs dbpats
        terSetPatterns dbpats $ do
        reportBody v
  {-
  -- if we are checking a delayed definition, we treat it as if there were
  -- a guarding coconstructor (sharp)
  terModifyGuarded (const $ case delayed of
        Delayed    -> Order.lt
        NotDelayed -> Order.le) $ do
  -}
        extract v
  where
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
            , nest 2 $ text "lhs:" <+> hsep (map prettyTCM pats)
            , nest 2 $ text "rhs:" <+> prettyTCM v
            ]

-- | Rewrite a clause @f ps =tel= \ {xs} -> v@ to @f ps {xs} =(tel {xs})= v@.
--   The pupose is to move hidden bounded size quantifications {j : Size< i}
--   to the lhs such that the termination checker can make use of them.
introHiddenLambdas :: MonadTCM tcm => Clause -> tcm Clause
introHiddenLambdas clause = liftTCM $ do
  case clause of
    Clause range ctel perm ps body Nothing -> return clause
    Clause range ctel perm ps body (Just t)-> do
      case removeHiddenLambdas body of
        -- nobody or no hidden lambdas
        ([], _) -> return clause
        -- hidden lambdas
        (axs, body') -> do
          -- n = number of hidden lambdas
          let n = length axs
          -- take n abstractions from rhs type
          TelV ttel t' <- telViewUpTo n $ unArg t
          when (size ttel < n) __IMPOSSIBLE__
          -- join with lhs telescope
          let ctel' = telFromList $ telToList ctel ++ telToList ttel
              ps'   = ps ++ map toPat axs
              perm' = liftP n perm
          return $ Clause range ctel' perm' ps' body' $ Just (t $> t')
  where
    toPat (Common.Arg (Common.ArgInfo h r c) x) =
           Common.Arg (Common.ArgInfo h r []) $ namedVarP x
    removeHiddenLambdas :: ClauseBody -> ([I.Arg ArgName], ClauseBody)
    removeHiddenLambdas = underBinds $ hlamsToBinds

    hlamsToBinds :: Term -> ([I.Arg ArgName], ClauseBody)
    hlamsToBinds v =
      case ignoreSharing v of
        Lam info b | getHiding info == Hidden ->
          let (xs, b') = hlamsToBinds $ unAbs b
          in  (Arg info (absName b) : xs, Bind $ b' <$ b)
        _ -> ([], Body v)
    underBinds :: (Term -> ([a], ClauseBody)) -> ClauseBody -> ([a], ClauseBody)
    underBinds k body = loop body where
      loop (Bind b) =
        let (res, b') = loop $ unAbs b
        in  (res, Bind $ b' <$ b)
      loop NoBody = ([], NoBody)
      loop (Body v) = k v

-- | Extract recursive calls from expressions.
class ExtractCalls a where
  extract :: a -> TerM Calls

instance ExtractCalls a => ExtractCalls (Abs a) where
  extract (NoAbs _ a) = extract a
  extract (Abs x a)   = addContext x $ terRaise $ extract a

instance ExtractCalls a => ExtractCalls (I.Arg a) where
  extract = extract . unArg

instance ExtractCalls a => ExtractCalls (I.Dom a) where
  extract = extract . unDom

instance ExtractCalls a => ExtractCalls (Elim' a) where
  extract Proj{}    = return CallGraph.empty
  extract (Apply a) = extract $ unArg a

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
        text "extracting calls from sort" <+> prettyTCM s
      reportSDoc "term.sort" 50 $
        text ("s = " ++ show s)
    case s of
      Prop       -> return CallGraph.empty
      Inf        -> return CallGraph.empty
      Type t     -> terUnguarded $ extract t  -- no guarded levels
      DLub s1 s2 -> extract (s1, s2)

-- | Extract recursive calls from a type.

instance ExtractCalls Type where
  extract (El s t) = extract (s, t)

{-
-- | Auxiliary type to write an instance of 'ExtractCalls'.

data TerConstructor = TerConstructor
  { terConsName      :: QName
    -- ^ Constructor name.
  , terConsInduction :: Induction
    -- ^ Should the constructor be treated as inductive or coinductive?
  , terConsArgs      :: [(I.Arg Term, Bool)]
    -- ^ All the arguments,
    --   and for every argument a boolean which is 'True' iff the
    --   argument should be viewed as preserving guardedness.
  }

-- | Extract recursive calls from a constructor application.

instance ExtractCalls TerConstructor where
  extract (TerConstructor c ind args) = mapM' loopArg args where
    loopArg (arg, preserves) = terModifyGuarded g' $ extract arg where
      g' = case (preserves, ind) of
             (True,  Inductive)   -> id
             (True,  CoInductive) -> (Order.lt .*.)
             (False, _)           -> const Order.unknown
-}

-- | Extract recursive calls from a constructor application.
constructor
  :: QName
    -- ^ Constructor name.
  -> Induction
    -- ^ Should the constructor be treated as inductive or coinductive?
  -> [(I.Arg Term, Bool)]
    -- ^ All the arguments,
    --   and for every argument a boolean which is 'True' iff the
    --   argument should be viewed as preserving guardedness.
  -> TerM Calls
constructor c ind args = do
  cutoff <- terGetCutOff
  let ?cutoff = cutoff
  mapM' loopArg args
  where
    loopArg (arg, preserves) = terModifyGuarded g' $ extract arg where
      g' = case (preserves, ind) of
             (True,  Inductive)   -> id
             (True,  CoInductive) -> (Order.lt .*.)
             (False, _)           -> const Order.unknown



-- | Handle guardedness preserving type constructor.

guardPresTyCon :: QName -> Elims -> (QName -> Elims -> TerM Calls) -> TerM Calls
guardPresTyCon g es cont = do
  ifNotM (terGetGuardingTypeConstructors) (cont g es) $ {- else -} do

    def <- liftTCM $ getConstInfo g
    let occs = defArgOccurrences def
        preserves = (StrictPos <=)
        -- Data or record type constructor.
        con = constructor g Inductive $   -- guardedness preserving
                zip (argsFromElims es)
                    (map preserves occs ++ repeat False)

    case theDef def of
      Datatype{} -> con
      Record{}   -> con
      _          -> cont g es


-- | Extract calls from with function application.

withFunction :: QName -> Elims -> TerM Calls
withFunction g es = do
  v <- liftTCM $ -- billTo [Benchmark.Termination, Benchmark.With] $  -- 0ms
         expandWithFunctionCall g es
  liftTCM $ reportSDoc "term.with.call" 30 $
    text "termination checking expanded with-function call:" <+> prettyTCM v
  extract v

-- | Handles function applications @g es@.

function :: QName -> Elims -> TerM Calls
function g es = ifM (terGetInlineWithFunctions `and2M` do isJust <$> isWithFunction g) (withFunction g es)
  $ {-else, no with function-} do

    f       <- terGetCurrent
    names   <- terGetMutual
    guarded <- terGetGuarded

    let gArgs = Def g es
    liftTCM $ reportSDoc "term.function" 30 $
      text "termination checking function call " <+> prettyTCM gArgs

    -- First, look for calls in the arguments of the call gArgs.

    -- We have to reduce constructors in case they're reexported.
    let reduceCon t = case ignoreSharing t of
           Con c vs -> (`apply` vs) <$> reduce (Con c [])  -- make sure we don't reduce the arguments
           _        -> return t

    -- Reduce constructors only when this call is actually a recursive one.
    -- es <- liftTCM $ billTo [Benchmark.Termination, Benchmark.Reduce] $ forM es $
    --         etaContract <=< traverse reduceCon <=< instantiateFull

    -- If the function is a projection but not for a coinductive record,
    -- then preserve guardedness for its principal argument.
    isProj <- isProjectionButNotCoinductive g
    let unguards = repeat Order.unknown
    let guards = applyWhen isProj (guarded :) unguards
    -- Collect calls in the arguments of this call.
    let args = map unArg $ argsFromElims es
    calls <- forM' (zip guards args) $ \ (guard, a) -> do
      terSetGuarded guard $ extract a

    -- Then, consider call gArgs itself.

    liftTCM $ reportSDoc "term.found.call" 20 $
      sep [ text "found call from" <+> prettyTCM f
          , nest 2 $ text "to" <+> prettyTCM g
          ]

    -- insert this call into the call list
    case List.elemIndex g names of

       -- call leads outside the mutual block and can be ignored
       Nothing   -> return calls

       -- call is to one of the mutally recursive functions
       Just gInd -> do
         delayed <- terGetDelayed
         pats    <- terGetPatterns
         -- 2014-03-25 Andreas, the costs seem small, benchmark turned off.
         es <- liftTCM $ -- billTo [Benchmark.Termination, Benchmark.Reduce] $
           forM es $
              etaContract <=< traverse reduceCon <=< instantiateFull

         -- Compute the call matrix.

         -- Andreas, 2014-03-26 only 6% of termination time for library test
         -- spent on call matrix generation
         (nrows, ncols, matrix) <- billTo [Benchmark.Termination, Benchmark.Compare] $ compareArgs es
         -- only a delayed definition can be guarded
         let ifDelayed o | Order.decreasing o && delayed == NotDelayed = Order.le
                         | otherwise                                  = o
         liftTCM $ reportSLn "term.guardedness" 20 $
           "composing with guardedness " ++ show guarded ++
           " counting as " ++ show (ifDelayed guarded)
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
         doc <- liftTCM $ buildClosure gArgs

         let src  = fromMaybe __IMPOSSIBLE__ $ List.elemIndex f names
             tgt  = gInd
             cm   = makeCM ncols nrows matrix'
             info = CallPath [CallInfo
                      { callInfoTarget = g
                      , callInfoRange  = getRange g
                      , callInfoCall   = doc
                      }]
         liftTCM $ reportSDoc "term.kept.call" 5 $ vcat
           [ text "kept call from" <+> text (show f) <+> hsep (map prettyTCM pats)
           , nest 2 $ text "to" <+> text (show g) <+>
                       hsep (map (parens . prettyTCM) args)
           , nest 2 $ text "call matrix (with guardedness): "
           , nest 2 $ pretty cm
           ]
         return $ CallGraph.insert src tgt cm info calls

-- | Extract recursive calls from a term.

instance ExtractCalls Term where
  extract t = do
    liftTCM $ reportSDoc "term.check.term" 50 $ do
      text "looking for calls in" <+> prettyTCM t

    -- Instantiate top-level MetaVar.
    t <- liftTCM $ instantiate t
    case ignoreSharing t of

      -- Constructed value.
      Con ConHead{conName = c} args -> do

        -- A constructor preserves the guardedness of all its arguments.
        let argsg = zip args $ repeat True

        -- If we encounter a coinductive record constructor
        -- in a type mutual with the current target
        -- then we count it as guarding.
        ind <- ifM ((Just c ==) <$> terGetSharp) (return CoInductive) $ do
          r <- liftTCM $ isRecordConstructor c
          case r of
            Nothing       -> return Inductive
            Just (q, def) -> (\ b -> if b then CoInductive else Inductive) <$>
              andM [ return $ recRecursive def
                   , return $ recInduction def == Just CoInductive
                   , targetElem (q : recMutual def)
                   ]
        constructor c ind argsg

      -- Function, data, or record type.
      Def g es -> guardPresTyCon g es function

      -- Abstraction. Preserves guardedness.
      Lam h b -> extract b

      -- Neutral term. Destroys guardedness.
      Var i es -> terUnguarded $ extract es

      -- Dependent function space.
      Pi a (Abs x b) -> CallGraph.union <$> (terUnguarded $ extract a) <*> do
         a <- maskSizeLt a  -- OR: just do not add a to the context!
         terPiGuarded $ addContext (x, a) $ terRaise $ extract b

      -- Non-dependent function space.
      Pi a (NoAbs _ b) -> CallGraph.union
         <$> terUnguarded (extract a)
         <*> terPiGuarded (extract b)

      -- Literal.
      Lit l -> return CallGraph.empty

      -- Sort.
      Sort s -> extract s

      -- Unsolved metas are not considered termination problems, there
      -- will be a warning for them anyway.
      MetaV x args -> return CallGraph.empty

      -- Erased and not-yet-erased proof.
      DontCare t -> extract t

      -- Level.
      Level l -> -- billTo [Benchmark.Termination, Benchmark.Level] $ do
        -- Andreas, 2014-03-26 Benchmark discontinued, < 0.3% spent on levels.
        extract l

      Shared{} -> __IMPOSSIBLE__
      ExtLam{} -> __IMPOSSIBLE__

-- | Extract recursive calls from level expressions.

deriving instance ExtractCalls Level

instance ExtractCalls PlusLevel where
  extract (ClosedLevel n) = return $ mempty
  extract (Plus n l)      = extract l

instance ExtractCalls LevelAtom where
  extract (MetaLevel x es)   = extract es
  extract (BlockedLevel x t) = extract t
  extract (NeutralLevel t)   = extract t
  extract (UnreducedLevel t) = extract t

-- | Rewrite type @tel -> Size< u@ to @tel -> Size@.
maskSizeLt :: MonadTCM tcm => I.Dom Type -> tcm (I.Dom Type)
maskSizeLt dom@(Dom info a) = liftTCM $ do
  (msize, msizelt) <- getBuiltinSize
  case (msize, msizelt) of
    (_ , Nothing) -> return dom
    (Nothing, _)  -> __IMPOSSIBLE__
    (Just size, Just sizelt) -> do
      TelV tel c <- telView a
      case ignoreSharingType a of
        El s (Def d [v]) | d == sizelt -> return $ Dom info $
          abstract tel $ El s $ Def size []
        _ -> return dom

{- | @compareArgs es@

     Compare the list of de Bruijn patterns (=parameters) @pats@
     with a list of arguments @es@ and create a call maxtrix
     with |es| rows and |pats| columns.

     The guardedness is the number of projection patterns in @pats@
     minus the number of projections in @es@.
 -}
compareArgs :: (Integral n) => [Elim] -> TerM (n, n, [[Order]])
compareArgs es = do
  pats <- terGetPatterns
  -- apats <- annotatePatsWithUseSizeLt pats
  -- reportSDoc "term.compare" 20 $
  --   text "annotated patterns = " <+> sep (map prettyTCM apats)
  -- matrix <- forM es $ \ e -> forM apats $ \ (b, p) -> terSetUseSizeLt b $ compareElim e p
  matrix <- withUsableVars pats $ forM es $ \ e -> forM pats $ \ p -> compareElim e p

  -- Count the number of coinductive projection(pattern)s in caller and callee
  projsCaller <- genericLength <$> do
    filterM isCoinductiveProjection $ mapMaybe isProjP pats
    -- filterM (not <.> isProjectionButNotCoinductive) $ mapMaybe isProjP pats
  projsCallee <- genericLength <$> do
    filterM isCoinductiveProjection $ mapMaybe isProjElim es
    -- filterM (not <.> isProjectionButNotCoinductive) $ mapMaybe isProjElim es
  cutoff <- terGetCutOff
  let ?cutoff = cutoff
  let guardedness = decr $ projsCaller - projsCallee
  liftTCM $ reportSLn "term.guardedness" 30 $
    "compareArgs: guardedness of call: " ++ show guardedness
  return $ addGuardedness guardedness (size es) (size pats) matrix

-- | Traverse patterns from left to right.
--   When we come to a projection pattern,
--   switch usage of SIZELT constraints:
--   on, if coinductive,
--   off, if inductive.
--
--   UNUSED
annotatePatsWithUseSizeLt :: [DeBruijnPat] -> TerM [(Bool,DeBruijnPat)]
annotatePatsWithUseSizeLt = loop where
  loop [] = return []
  loop (p@(ProjDBP q) : pats) = ((False,p) :) <$> do projUseSizeLt q $ loop pats
  loop (p : pats) = (\ b ps -> (b,p) : ps) <$> terGetUseSizeLt <*> loop pats


-- | @compareElim e dbpat@

compareElim :: Elim -> DeBruijnPat -> TerM Order
compareElim e p = do
  liftTCM $ do
    reportSDoc "term.compare" 30 $ sep
      [ text "compareElim"
      , nest 2 $ text "e = " <+> prettyTCM e
      , nest 2 $ text "p = " <+> prettyTCM p
      ]
    reportSDoc "term.compare" 50 $ sep
      [ nest 2 $ text $ "e = " ++ show e
      , nest 2 $ text $ "p = " ++ show p
      ]
  case (e, p) of
    (Proj d, ProjDBP d')           -> compareProj d d'
    (Proj{}, _         )           -> return Order.unknown
    (Apply{}, ProjDBP{})           -> return Order.unknown
    (Apply arg, p)                 -> compareTerm (unArg arg) p

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
              case (find (d==) fs, find (d'==) fs) of
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

{- To turn off guardedness, restore this code.
-- | 'addGuardedness' does nothing.
addGuardedness :: Integral n => Order -> n -> n -> [[Order]] -> (n, n, [[Order]])
addGuardedness g nrows ncols m = (nrows, ncols, m)
-}

-- | 'addGuardedness' adds guardedness flag in the upper left corner (0,0).
addGuardedness :: Integral n => Order -> n -> n -> [[Order]] -> (n, n, [[Order]])
addGuardedness o nrows ncols m =
  (nrows + 1, ncols + 1,
   (o : genericReplicate ncols Order.unknown) : map (Order.unknown :) m)

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

-- | Compute the sub patterns of a 'DeBruijnPat'.
subPatterns :: DeBruijnPat -> [DeBruijnPat]
subPatterns p = case p of
  VarDBP _    -> []
  ConDBP c ps -> ps ++ concatMap subPatterns ps
  LitDBP _    -> []
  ProjDBP _   -> []

compareTerm :: Term -> DeBruijnPat -> TerM Order
compareTerm t p = do
--   reportSDoc "term.compare" 25 $
--     text " comparing term " <+> prettyTCM t <+>
--     text " to pattern " <+> prettyTCM p
  t <- liftTCM $ stripAllProjections t
  o <- compareTerm' t p
  liftTCM $ reportSDoc "term.compare" 25 $
    text " comparing term " <+> prettyTCM t <+>
    text " to pattern " <+> prettyTCM p <+>
    text (" results in " ++ show o)
  return o
{-
compareTerm t p = Order.supremum $ compareTerm' t p : map cmp (subPatterns p)
  where
    cmp p' = (Order..*.) Order.lt (compareTerm' t p')
-}


-- | Remove all non-coinductive projections from an algebraic term
--   (not going under binders).
--   Also, remove 'DontCare's.
class StripAllProjections a where
  stripAllProjections :: a -> TCM a

instance StripAllProjections a => StripAllProjections (I.Arg a) where
  stripAllProjections = traverse stripAllProjections
  -- stripAllProjections (Arg info a) = Arg info <$> stripAllProjections a

{- DOES NOT WORK, since s.th. special is needed for Elims
instance StripAllProjections a => StripAllProjections [a] where
  stripAllProjections = traverse stripAllProjections

instance StripAllProjections a => StripAllProjections (Elim' a) where
-}

instance StripAllProjections Elims where
  stripAllProjections es =
    case es of
      []             -> return []
      (Apply a : es) -> do
        (:) <$> (Apply <$> stripAllProjections a) <*> stripAllProjections es
      (Proj p  : es) -> do
        isP <- isProjectionButNotCoinductive p
        applyUnless isP (Proj p :) <$> stripAllProjections es

instance StripAllProjections Args where
  stripAllProjections = mapM stripAllProjections

instance StripAllProjections Term where
  stripAllProjections t = do
    case ignoreSharing t of
      Var i es   -> Var i <$> stripAllProjections es
      Con c ts   -> Con c <$> stripAllProjections ts
      Def d es   -> Def d <$> stripAllProjections es
      DontCare t -> stripAllProjections t
      _ -> return t

-- | @compareTerm' t dbpat@
--
--   Precondition: top meta variable resolved

compareTerm' :: Term -> DeBruijnPat -> TerM Order
compareTerm' v0 p = do
  suc  <- terGetSizeSuc
  cutoff <- terGetCutOff
  let ?cutoff = cutoff
  let v = ignoreSharing v0
  case (v, p) of

    -- Andreas, 2013-11-20 do not drop projections,
    -- in any case not coinductive ones!:
    (Var i es, p) | Just{} <- allApplyElims es ->
      compareVar i p

    (DontCare t, p) ->
      compareTerm' t p

    (Lit l, LitDBP l')
      | l == l'     -> return Order.le
      | otherwise   -> return Order.unknown

    (Lit l, p) -> do
      v <- liftTCM $ constructorForm v
      case ignoreSharing v of
        Lit{}       -> return Order.unknown
        v           -> compareTerm' v p

    -- Andreas, 2011-04-19 give subterm priority over matrix order

    (Con{}, ConDBP c ps) | any (isSubTerm v) ps ->
      decrease <$> offsetFromConstructor c <*> return Order.le

    (Con c ts, ConDBP c' ps) | conName c == c'->
      compareConArgs ts ps

    (Def s [Apply t], ConDBP s' [p]) | s == s' && Just s == suc ->
      compareTerm' (unArg t) p

    -- new cases for counting constructors / projections
    -- register also increase
    (Def s [Apply t], p) | Just s == suc ->
      -- Andreas, 2012-10-19 do not cut off here
      increase 1 <$> compareTerm' (unArg t) p

    (Con c [], p) -> return Order.le

    (Con c ts, p) -> do
      increase <$> offsetFromConstructor (conName c)
               <*> (infimum <$> mapM (\ t -> compareTerm' (unArg t) p) ts)

    (t, p) | isSubTerm t p -> return Order.le

    _ -> return Order.unknown

-- TODO: isSubTerm should compute a size difference (Order)
isSubTerm :: Term -> DeBruijnPat -> Bool
isSubTerm t p = equal t p || properSubTerm t p
  where
    equal (Shared p) dbp = equal (derefPtr p) dbp
    equal (Con c ts) (ConDBP c' ps) =
      and $ (conName c == c')
          : (length ts == length ps)
          : zipWith equal (map unArg ts) ps
    equal (Var i []) (VarDBP j) = i == j
    equal (Lit l) (LitDBP l') = l == l'
    equal _ _ = False

    properSubTerm t (ConDBP _ ps) = any (isSubTerm t) ps
    properSubTerm _ _ = False

compareConArgs :: Args -> [DeBruijnPat] -> TerM Order
compareConArgs ts ps = do
  cutoff <- terGetCutOff
  let ?cutoff = cutoff
  -- we may assume |ps| >= |ts|, otherwise c ps would be of functional type
  -- which is impossible
  case (length ts, length ps) of
    (0,0) -> return Order.le        -- c <= c
    (0,1) -> return Order.unknown   -- c not<= c x
    (1,0) -> __IMPOSSIBLE__
    (1,1) -> compareTerm' (unArg (head ts)) (head ps)
    (_,_) -> foldl (Order..*.) Order.le <$>
               zipWithM compareTerm' (map unArg ts) ps
       -- corresponds to taking the size, not the height
       -- allows examples like (x, y) < (Succ x, y)
{- version which does an "order matrix"
   -- Andreas, 2013-02-18 disabled because it is unclear
   -- how to scale idempotency test to matrix-shaped orders (need thinking/researcH)
   -- Trigges issue 787.
        (_,_) -> do -- build "call matrix"
          m <- mapM (\t -> mapM (compareTerm' suc (unArg t)) ps) ts
          let m2 = makeCM (genericLength ps) (genericLength ts) m
          return $ Order.orderMat (Order.mat m2)
-}
{- version which takes height
--    if null ts then Order.Le
--               else Order.infimum (zipWith compareTerm' (map unArg ts) ps)
-}

compareVar :: Nat -> DeBruijnPat -> TerM Order
compareVar i (VarDBP j)    = compareVarVar i j
compareVar i (LitDBP _)    = return $ Order.unknown
compareVar i (ProjDBP _)   = return $ Order.unknown
compareVar i (ConDBP c ps) = do
  cutoff <- terGetCutOff
  let ?cutoff = cutoff
  decrease <$> offsetFromConstructor c
           <*> (Order.supremum <$> mapM (compareVar i) ps)

-- | Compare two variables.
--
--   The first variable comes from a term, the second from a pattern.
compareVarVar :: Nat -> Nat -> TerM Order
compareVarVar i j
  | i == j    = return Order.le
  | otherwise = ifNotM ((i `VarSet.member`) <$> terGetUsableVars) (return Order.unknown) $ {- else -} do
      res <- isBounded i
      case res of
        BoundedNo  -> return Order.unknown
        BoundedLt v -> decrease 1 <$> compareTerm' v (VarDBP j)
