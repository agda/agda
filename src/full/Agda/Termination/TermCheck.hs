{-# LANGUAGE CPP, PatternGuards, ImplicitParams, TupleSections, NamedFieldPuns,
             FlexibleInstances, TypeSynonymInstances,
             DeriveFunctor #-}

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

import Agda.Termination.Monad
import Agda.Termination.CallGraph   as Term
import qualified Agda.Termination.SparseMatrix as Matrix
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
import Agda.TypeChecking.Primitive (constructorForm)
import Agda.TypeChecking.Level (reallyUnLevelView)
import Agda.TypeChecking.Substitute
import Agda.TypeChecking.SizedTypes

import Agda.Interaction.Options

import Agda.Utils.Function
import Agda.Utils.List
import Agda.Utils.Size
import Agda.Utils.Maybe
import Agda.Utils.Monad -- (mapM', forM', ifM, or2M, and2M, (<.>))
import Agda.Utils.Pointed
import Agda.Utils.Permutation

#include "../undefined.h"
import Agda.Utils.Impossible


-- | The call information is stored as free monoid
--   over 'CallInfo'.  As long as we never look at it,
--   only accumulate it, it does not matter whether we use
--   'Set', (nub) list, or 'Tree'.
--   Internally, due to lazyness, it is anyway a binary tree of
--   'mappend' nodes and singleton leafs.
--   Since we define no order on 'CallInfo' (expensive),
--   we cannot use a 'Set' or nub list.
--   Performance-wise, I could not see a difference between Set and list.

type Calls = Term.CallGraph [CallInfo]


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
        -- open is just an artifact from the concrete syntax
    A.ScopedDecl{}        -> __IMPOSSIBLE__
        -- taken care of above
    A.RecSig{}            -> return mempty
    A.RecDef _ r _ _ _ _ ds -> checkRecDef [] r ds
    -- These should all be wrapped in mutual blocks
    A.FunDef{}  -> __IMPOSSIBLE__
    A.DataSig{} -> __IMPOSSIBLE__
    A.DataDef{} -> __IMPOSSIBLE__
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
      -- no need to term-check if the declarations are acyclic
      skip = not <$> recursive allNames

  -- Skip termination check when asked by pragma or no recursion.
  ifM (return (not (Info.mutualTermCheck i)) `or2M` skip) (do
      reportSLn "term.warn.yes" 2 $ "Skipping termination check for " ++ show names
      forM_ allNames $ \ q -> setTerminates q True -- considered terminating!
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

     let tenv = defaultTerEnv
           { terGuardingTypeConstructors = guardingTypeConstructors
           , terSizeSuc                  = suc
           , terSharp                    = sharp
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
     let terminates = null res
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
  r <- case Term.terminates calls1 of
         r@Right{} -> return r
         Left{}    -> do
           -- Try again, but include the dot patterns this time.
           calls2 <- terSetUseDotPatterns True $ collect
           reportCalls "" calls2
           return $ Term.terminates calls2

  -- @names@ is taken from the 'Abstract' syntax, so it contains only
  -- the names the user has declared.  This is for error reporting.
  names <- terGetUserNames
  case r of
    Left calls -> do
      return $ point $ TerminationError
                { termErrFunctions = names
                , termErrCalls     = calls
                }
    Right{} -> do
      liftTCM $ reportSLn "term.warn.yes" 2 $
        show (names) ++ " does termination check"
      return mempty

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
         cs0     = completionInit calls
         step cs = do
           let cs' = completionStep cs0 cs
               diff = CallGraph $ theCallGraph cs' Map.\\ theCallGraph cs
           report " New call matrices " diff
           return cs'
     report " Initial call matrices " cs0
     void $ iterateUntilM notWorse step cs0

   -- Print the result of completion.
   let calls' = Term.complete calls
       (idems, others) = List.partition (Term.idempotent . fst) $
         Term.toList calls'
   reportSDoc "term.behaviours" 20 $ vcat
     [ text $ "Recursion behaviours (" ++ no ++ "dot patterns):"
     , nest 2 $ return $ Term.prettyBehaviour calls'
     ]
   reportSDoc "term.matrices" 30 $ vcat
     [ text $ "Idempotent call matrices (" ++ no ++ "dot patterns):"
     , nest 2 $ pretty $ Term.fromList idems
     ]
   reportSDoc "term.matrices" 30 $ vcat
     [ text $ "Other call matrices (" ++ no ++ "dot patterns):"
     , nest 2 $ pretty $ Term.fromList others
     ]

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
    case Term.terminatesFilter (== index) calls1 of
      r@Right{} -> return r
      Left{}    -> do
        -- Try again, but include the dot patterns this time.
        calls2 <- terSetUseDotPatterns True $ collect
        reportCalls "" calls2
        return $ Term.terminatesFilter (== index) calls2

   names <- terGetUserNames
   case r of
     Left calls -> do
       return $ point $ TerminationError
         { termErrFunctions = if name `elem` names then [name] else []
         , termErrCalls     = calls
         }
     Right{} -> do
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

  liftTCM $ reportSDoc "term.def.fun" 5 $
    sep [ text "termination checking body of" <+> prettyTCM name
        , nest 2 $ text ":" <+> (prettyTCM $ defType def)
        ]

  case theDef def of
    Function{ funClauses = cls, funDelayed = delayed } ->
      terSetDelayed delayed $ forM' cls $ termClause

    _ -> return Term.empty


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
      Nothing -> return Term.empty
      Just v -> do
        dbpats <- mapM stripCoConstructors dbpats
        terSetPatterns dbpats $ do
        reportBody v
  {-
  -- if we are checking a delayed definition, we treat it as if there were
  -- a guarding coconstructor (sharp)
  terModifyGuarded (const $ case delayed of
        Delayed    -> Term.lt
        NotDelayed -> Term.le) $ do
  -}
        extract v
  where
    reportBody :: Term -> TerM ()
    reportBody v = do
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
           Common.Arg (Common.ArgInfo h r []) $ Named (Just x) $ VarP x
    removeHiddenLambdas :: ClauseBody -> ([I.Arg String], ClauseBody)
    removeHiddenLambdas = underBinds $ hlamsToBinds

    hlamsToBinds :: Term -> ([I.Arg String], ClauseBody)
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
  extract Proj{}    = return Term.empty
  extract (Apply a) = extract $ unArg a

instance ExtractCalls a => ExtractCalls [a] where
  extract = mapM' extract

instance (ExtractCalls a, ExtractCalls b) => ExtractCalls (a,b) where
  extract (a, b) = Term.union <$> extract a <*> extract b

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
    -- s <- instantiateFull s -- Andreas, 2012-09-05 NOT NECESSARY
    -- instantiateFull resolves problems with reallyUnLevelView
    -- in the absense of level built-ins.
    -- However, the termination checker should only receive terms
    -- that are already fully instantiated.
    case s of
      Prop                       -> return Term.empty
      Inf                        -> return Term.empty
      Type (Max [])              -> return Term.empty
      Type (Max [ClosedLevel{}]) -> return Term.empty
      Type t                     -> terSetGuarded Term.unknown $
        extract $ Level t    -- no guarded levels
      DLub s1 s2                 -> extract (s1, s2)

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
             (True,  CoInductive) -> (Term.lt .*.)
             (False, _)           -> const Term.unknown
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
             (True,  CoInductive) -> (Term.lt .*.)
             (False, _)           -> const Term.unknown



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
  v <- liftTCM $ expandWithFunctionCall g es
  liftTCM $ reportSDoc "term.with.call" 30 $
    text "termination checking expanded with-function call:" <+> prettyTCM v
  extract v

-- | Handles function applications @g es@.

function :: QName -> Elims -> TerM Calls
function g es = ifJustM (isWithFunction g) (\ _ -> withFunction g es)
  $ {-else, no with function-} do

    f       <- terGetCurrent
    names   <- terGetMutual
    guarded <- terGetGuarded

    let gArgs = Def g es
    liftTCM $ reportSDoc "term.function" 30 $
      text "termination checking function call " <+> prettyTCM gArgs

    -- We have to reduce constructors in case they're reexported.
    let reduceCon t = case ignoreSharing t of
           Con c vs -> (`apply` vs) <$> reduce (Con c [])  -- make sure we don't reduce the arguments
           _        -> return t
    es <- liftTCM $ forM es $
            etaContract <=< traverse reduceCon <=< instantiateFull

    -- If the function is a projection but not for a coinductive record,
    -- then preserve guardedness for its principal argument.
    isProj <- isProjectionButNotCoinductive g
    let unguards = repeat Term.unknown
    let guards = if isProj then guarded : unguards
                                -- proj => preserve guardedness of principal argument
                           else unguards -- not a proj ==> unguarded
    -- collect calls in the arguments of this call
    let args = map unArg $ argsFromElims es
    calls <- forM' (zip guards args) $ \ (guard, a) -> do
      terSetGuarded guard $ extract a

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

         (nrows, ncols, matrix) <- compareArgs es
         -- only a delayed definition can be guarded
         let ifDelayed o | Term.decreasing o && delayed == NotDelayed = Term.le
                         | otherwise                                  = o
         liftTCM $ reportSLn "term.guardedness" 20 $
           "composing with guardedness " ++ show guarded ++
           " counting as " ++ show (ifDelayed guarded)
         cutoff <- terGetCutOff
         let ?cutoff = cutoff
         let matrix' = composeGuardedness (ifDelayed guarded) matrix

         liftTCM $ reportSDoc "term.kept.call" 5
           (sep [ text "kept call from" <+> prettyTCM f
                   <+> hsep (map prettyTCM pats)
                , nest 2 $ text "to" <+> prettyTCM g <+>
                            hsep (map (parens . prettyTCM) args)
                , nest 2 $ text ("call matrix (with guardedness): " ++ show matrix')
                ])

         -- Andreas, 2013-05-19 as pointed out by Andrea Vezzosi,
         -- printing the call eagerly is forbiddingly expensive.
         -- So we build a closure such that we can print the call
         -- whenever we really need to.
         -- This saves 30s (12%) on the std-lib!
         doc <- liftTCM $ buildClosure gArgs
         let call = Term.Call
                      { Term.source = fromMaybe __IMPOSSIBLE__ $
                          List.elemIndex f names
                      , Term.target = gInd
                      , Term.cm     = makeCM ncols nrows matrix'
                      }
             info = point $ CallInfo
                      { callInfoRange = getRange g
                      , callInfoCall  = doc
                      }
         return $ Term.insert call info calls

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
                   , return $ recInduction def == CoInductive
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
      Pi a (Abs x b) -> Term.union <$> (terUnguarded $ extract a) <*> do
         a <- maskSizeLt a  -- OR: just do not add a to the context!
         terPiGuarded $ addCtxString x a $ terRaise $ extract b

      -- Non-dependent function space.
      Pi a (NoAbs _ b) -> Term.union
         <$> terUnguarded (extract a)
         <*> terPiGuarded (extract b)

      -- Literal.
      Lit l -> return Term.empty

      -- Sort.
      Sort s -> extract s

      -- Unsolved metas are not considered termination problems, there
      -- will be a warning for them anyway.
      MetaV x args -> return Term.empty

      -- Erased and not-yet-erased proof.
      DontCare t -> extract t

      -- Level.
      Level l -> do
        l <- catchError (liftTCM $ reallyUnLevelView l) $ \ err -> do
          internalError $
            "Termination checker: cannot view level expression, " ++
            "probably due to missing level built-ins."
        extract l

      Shared{} -> __IMPOSSIBLE__

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
compareArgs :: (Integral n) => [Elim] -> TerM (n, n, [[Term.Order]])
compareArgs es = do
  pats <- terGetPatterns
  -- matrix <- forM es $ forM pats . compareTerm suc  -- UNREADABLE pointfree style
  matrix <- forM es $ \ e -> forM pats $ \ p -> compareElim e p

  -- Count the number of coinductive projection(pattern)s in caller and callee
  projsCaller <- genericLength <$> do
    filterM (not <.> isProjectionButNotCoinductive) $ mapMaybe isProjP pats
  projsCallee <- genericLength <$> do
    filterM (not <.> isProjectionButNotCoinductive) $ mapMaybe isProjElim es
  cutoff <- terGetCutOff
  let ?cutoff = cutoff
  let guardedness = decr $ projsCaller - projsCallee
  liftTCM $ reportSLn "term.guardedness" 30 $
    "compareArgs: guardedness of call: " ++ show guardedness
  return $ addGuardedness guardedness (size es) (size pats) matrix

-- | @compareElim e dbpat@

compareElim :: Elim -> DeBruijnPat -> TerM Term.Order
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
    (Proj{}, _         )           -> return Term.unknown
    (Apply{}, ProjDBP{})           -> return Term.unknown
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
compareProj :: MonadTCM tcm => QName -> QName -> tcm Term.Order
compareProj d d'
  | d == d' = return Term.le
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
                  | i < i'    -> return Term.lt
                  | i == i'   -> do
                     __IMPOSSIBLE__
                  | otherwise -> return Term.unknown
                _ -> __IMPOSSIBLE__
            _ -> __IMPOSSIBLE__
        _ -> return Term.unknown

-- | 'makeCM' turns the result of 'compareArgs' into a proper call matrix
makeCM :: Index -> Index -> [[Term.Order]] -> Term.CallMatrix
makeCM ncols nrows matrix = Term.CallMatrix $
  Matrix.fromLists (Matrix.Size nrows ncols) matrix

{- To turn off guardedness, restore this code.
-- | 'addGuardedness' does nothing.
addGuardedness :: Integral n => Order -> n -> n -> [[Term.Order]] -> (n, n, [[Term.Order]])
addGuardedness g nrows ncols m = (nrows, ncols, m)
-}

-- | 'addGuardedness' adds guardedness flag in the upper left corner (0,0).
addGuardedness :: Integral n => Order -> n -> n -> [[Term.Order]] -> (n, n, [[Term.Order]])
addGuardedness o nrows ncols m =
  (nrows + 1, ncols + 1,
   (o : genericReplicate ncols Term.unknown) : map (Term.unknown :) m)

-- | Compose something with the upper-left corner of a call matrix
composeGuardedness :: (?cutoff :: CutOff) => Term.Order -> [[Term.Order]] -> [[Term.Order]]
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

compareTerm :: Term -> DeBruijnPat -> TerM Term.Order
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
compareTerm t p = Term.supremum $ compareTerm' t p : map cmp (subPatterns p)
  where
    cmp p' = (Term..*.) Term.lt (compareTerm' t p')
-}

-- | For termination checking purposes flat should not be considered a
--   projection. That is, it flat doesn't preserve either structural order
--   or guardedness like other projections do.
--   Andreas, 2012-06-09: the same applies to projections of recursive records.
isProjectionButNotCoinductive :: MonadTCM tcm => QName -> tcm Bool
isProjectionButNotCoinductive qn = liftTCM $ do
  b <- isProjectionButNotCoinductive' qn
  reportSDoc "term.proj" 60 $ do
    text "identifier" <+> prettyTCM qn <+> do
      text $
        if b then "is an inductive projection"
          else "is either not a projection or coinductive"
  return b
  where
    isProjectionButNotCoinductive' qn = do
      flat <- fmap nameOfFlat <$> coinductionKit
      if Just qn == flat
        then return False
        else do
          mp <- isProjection qn
          case mp of
            Just Projection{ projProper = Just{}, projFromType }
              -> isInductiveRecord projFromType
            _ -> return False


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
        (if isP then id else (Proj p :)) <$> stripAllProjections es

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

compareTerm' :: Term -> DeBruijnPat -> TerM Term.Order
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
      | l == l'     -> return Term.le
      | otherwise   -> return Term.unknown

    (Lit l, p) -> do
      v <- liftTCM $ constructorForm v
      case ignoreSharing v of
        Lit{}       -> return Term.unknown
        v           -> compareTerm' v p

    -- Andreas, 2011-04-19 give subterm priority over matrix order

    (Con{}, ConDBP c ps) | any (isSubTerm v) ps ->
      decrease <$> offsetFromConstructor c <*> return Term.le

    (Con c ts, ConDBP c' ps) | conName c == c'->
      compareConArgs ts ps

    (Def s [Apply t], ConDBP s' [p]) | s == s' && Just s == suc ->
      compareTerm' (unArg t) p

    -- new cases for counting constructors / projections
    -- register also increase
    (Def s [Apply t], p) | Just s == suc ->
      -- Andreas, 2012-10-19 do not cut off here
      increase 1 <$> compareTerm' (unArg t) p

    (Con c [], p) -> return Term.le

    (Con c ts, p) -> do
      increase <$> offsetFromConstructor (conName c)
               <*> (infimum <$> mapM (\ t -> compareTerm' (unArg t) p) ts)

    (t, p) | isSubTerm t p -> return Term.le

    _ -> return Term.unknown

-- TODO: isSubTerm should compute a size difference (Term.Order)
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

compareConArgs :: Args -> [DeBruijnPat] -> TerM Term.Order
compareConArgs ts ps = do
  cutoff <- terGetCutOff
  let ?cutoff = cutoff
  -- we may assume |ps| >= |ts|, otherwise c ps would be of functional type
  -- which is impossible
  case (length ts, length ps) of
    (0,0) -> return Term.le        -- c <= c
    (0,1) -> return Term.unknown   -- c not<= c x
    (1,0) -> __IMPOSSIBLE__
    (1,1) -> compareTerm' (unArg (head ts)) (head ps)
    (_,_) -> foldl (Term..*.) Term.le <$>
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
          return $ Term.orderMat (Term.mat m2)
-}
{- version which takes height
--    if null ts then Term.Le
--               else Term.infimum (zipWith compareTerm' (map unArg ts) ps)
-}

compareVar :: Nat -> DeBruijnPat -> TerM Term.Order
compareVar i (VarDBP j)    = compareVarVar i j
compareVar i (LitDBP _)    = return $ Term.unknown
compareVar i (ProjDBP _)   = return $ Term.unknown
compareVar i (ConDBP c ps) = do
  cutoff <- terGetCutOff
  let ?cutoff = cutoff
  decrease <$> offsetFromConstructor c
           <*> (Term.supremum <$> mapM (compareVar i) ps)

-- | Compare two variables
compareVarVar :: Nat -> Nat -> TerM Term.Order
compareVarVar i j
  | i == j    = return Term.le
  | otherwise = do
      res <- isBounded i
      case res of
        BoundedNo  -> return Term.unknown
        BoundedLt v -> decrease 1 <$> compareTerm' v (VarDBP j)

