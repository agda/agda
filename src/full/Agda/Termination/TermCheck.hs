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
import Data.Maybe (mapMaybe, isJust)
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

type MutualNames = [QName]

-- | The result of termination checking a module.
--   Must be 'Pointed' and a 'Monoid'.
type Result = [TerminationError]

-- | Termination check a single declaration.
termDecl :: A.Declaration -> TCM Result
termDecl d = ignoreAbstractMode $ termDecl' d

-- | Termination check a sequence of declarations.
termDecls :: [A.Declaration] -> TCM Result
termDecls ds = concat <$> mapM termDecl' ds

-- | Termination check a single declaration (without necessarily
-- ignoring @abstract@).
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

-- | Termination check a bunch of mutually inductive recursive definitions.
termMutual :: Info.MutualInfo -> [A.Declaration] -> TCM Result
termMutual i ds = if names == [] then return mempty else
  -- we set the range to avoid panics when printing error messages
  traceCall (SetRange (Info.mutualRange i)) $ do

  mutualBlock <- findMutualBlock (head names)
  let allNames = Set.elems mutualBlock
      -- no need to term-check if the declarations are acyclic
      skip = not <$> recursive allNames

  ifM (return (not (Info.mutualTermCheck i)) `or2M` skip) (do
      reportSLn "term.warn.yes" 2 $ "Skipping termination check for " ++ show names
      forM_ allNames $ \ q -> setTerminates q True -- considered terminating!
      return mempty)
   $ do
     -- get list of sets of mutually defined names from the TCM
     -- this includes local and auxiliary functions introduced
     -- during type-checking

     cutoff <- optTerminationDepth <$> pragmaOptions
     let ?cutoff = cutoff -- needed for Term.terminates

     reportSLn "term.top" 10 $ "Termination checking " ++ show names ++
       " with cutoff=" ++ show cutoff ++ "..."

     -- Get the name of size suc (if sized types are enabled)
     suc <- sizeSucName

     -- The name of sharp (if available).
     sharp <- fmap nameOfSharp <$> coinductionKit

     guardingTypeConstructors <-
       optGuardingTypeConstructors <$> pragmaOptions

     let conf = DBPConf
           { useDotPatterns           = False
           , guardingTypeConstructors = guardingTypeConstructors
           , withSizeSuc              = suc
           , sharp                    = sharp
           , currentTarget            = Nothing
           }

     -- new check currently only makes a difference for copatterns
     -- since it is slow, only invoke it if --copatterns
     res <- ifM (optCopatterns <$> pragmaOptions)
       (forM' allNames $ termFunction conf names allNames) -- new check one after another
       (termMutual' conf names allNames) -- old check, all at once

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


-- | @termMutual' conf names allNames@ checks @allNames@ for termination.
--
--   @names@ is taken from the 'Abstract' syntax, so it contains only
--   the names the user has declared.  This is for error reporting.
--
--   @allNames@ is taken from 'Internal' syntax, it contains also
--   the definitions created by the type checker (e.g., with-functions).
--
termMutual' :: (?cutoff :: CutOff) => DBPConf -> [QName] -> MutualNames -> TCM Result
termMutual' conf names allNames = do

     -- collect all recursive calls in the block
     let collect conf = mapM' (termDef conf allNames) allNames

     -- first try to termination check ignoring the dot patterns
     calls1 <- collect conf{ useDotPatterns = False }
     reportCalls "no " calls1

     r <- case Term.terminates calls1 of
            r@Right{} -> return r
            Left{}    -> do
              -- Try again, but include the dot patterns this time.
              calls2 <- collect conf{ useDotPatterns = True }
              reportCalls "" calls2
              return $ Term.terminates calls2
     case r of
       Left calls -> do
         return $ point $ TerminationError
                   { termErrFunctions = names
                   , termErrCalls     = calls
                   }
       Right _ -> do
         reportSLn "term.warn.yes" 2
                     (show (names) ++ " does termination check")
         return mempty
  where

reportCalls no calls = do
   reportS "term.lex" 20 $ unlines
     [ "Calls (" ++ no ++ "dot patterns): " ++ show calls
     ]

   -- Print the whole completion phase
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

   -- Print the result of completion
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

-- | @termFunction conf names allNames name@ checks @name@ for termination.
--
--   @names@ is taken from the 'Abstract' syntax, so it contains only
--   the names the user has declared.  This is for error reporting.
--
--   @allNames@ is taken from 'Internal' syntax, it contains also
--   the definitions created by the type checker (e.g., with-functions).
--
termFunction :: (?cutoff :: CutOff) => DBPConf -> [QName] -> MutualNames -> QName -> TCM Result
termFunction conf0 names allNames name = do

     let index = toInteger $ maybe __IMPOSSIBLE__ id $
           List.elemIndex name allNames

     conf <- do
       r <- typeEndsInDef =<< typeOfConst name
       reportTarget r
       return $ conf0 { currentTarget = r }

     -- collect all recursive calls in the block
     let collect conf = mapM' (termDef conf allNames) allNames

     -- first try to termination check ignoring the dot patterns
     calls1 <- collect conf{ useDotPatterns = False }
     reportCalls "no " calls1

     r <- case Term.terminatesFilter (== index) calls1 of
            r@Right{} -> return r
            Left{}    -> do
              -- Try again, but include the dot patterns this time.
              calls2 <- collect conf{ useDotPatterns = True }
              reportCalls "" calls2
              return $ Term.terminatesFilter (== index) calls2
     case r of
       Left calls -> do
         return $ point $ TerminationError
                   { termErrFunctions = if name `elem` names then [name] else []
                   , termErrCalls     = calls
                   }
       Right _ -> do
         reportSLn "term.warn.yes" 2
                     (show (name) ++ " does termination check")
         return mempty
  where
    reportTarget r = reportSLn "term.target" 20 $ maybe
      ("  target type not recognized")
      (\ q -> "  target type ends in " ++ show q)
      r

typeEndsInDef :: Type -> TCM (Maybe QName)
typeEndsInDef t = do
  TelV _ core <- telView t
  case ignoreSharing $ unEl core of
    Def d vs -> return $ Just d
    _        -> return Nothing

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


-- | Termination check a definition by pattern matching.
termDef :: DBPConf -> MutualNames -> QName -> TCM Calls
termDef use names name = do
	-- Retrieve definition
        def <- getConstInfo name
        -- returns a TC.Monad.Base.Definition

	reportSDoc "term.def.fun" 5 $
	  sep [ text "termination checking body of" <+> prettyTCM name
	      , nest 2 $ text ":" <+> (prettyTCM $ defType def)
	      ]
        case (theDef def) of
          Function{ funClauses = cls, funDelayed = delayed } ->
            mapM' (termClause use names name delayed) cls
          _ -> return Term.empty


-- | Termination check clauses
{- Precondition: Each clause headed by the same number of patterns

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

data DeBruijnPat' a
  = VarDBP a  -- ^ De Bruijn Index.
  | ConDBP QName [DeBruijnPat' a]
    -- ^ The name refers to either an ordinary
    --   constructor or the successor function on sized types.
  | LitDBP Literal
  | ProjDBP QName
  deriving (Functor, Show)

type DeBruijnPat = DeBruijnPat' Nat

instance IsProjP (DeBruijnPat' a) where
  isProjP (ProjDBP d) = Just d
  isProjP _           = Nothing

instance PrettyTCM DeBruijnPat where
  prettyTCM (VarDBP i)    = text $ show i
  prettyTCM (ConDBP c ps) = parens (prettyTCM c <+> hsep (map prettyTCM ps))
  prettyTCM (LitDBP l)    = prettyTCM l
  prettyTCM (ProjDBP d)   = prettyTCM d

unusedVar :: DeBruijnPat
unusedVar = LitDBP (LitString noRange "term.unused.pat.var")

{- | liftDeBruijnPat p n

     increases each de Bruijn index in p by n.
     Needed when going under a binder during analysis of a term.
-}

liftDBP :: DeBruijnPat -> DeBruijnPat
liftDBP = fmap (1+) -- adjIndexDBP (1+)

{- | Configuration parameters to termination checker.
-}
data DBPConf = DBPConf
  { useDotPatterns           :: Bool
  , guardingTypeConstructors :: Bool
    -- ^ Do we assume that record and data type constructors preserve guardedness?
  , withSizeSuc              :: Maybe QName
  , sharp                    :: Maybe QName
    -- ^ The name of the sharp constructor, if any.
  , currentTarget            :: Maybe Target
    -- ^ Target type of the function we are currently termination checking.
    --   Only the constructors of 'Target' are considered guarding.
  }

type Target = QName

targetElem :: DBPConf -> [Target] -> Bool
targetElem conf ds = maybe False (`elem` ds) (currentTarget conf)

{-
-- | Check wether a 'Target" corresponds to the current one.
matchingTarget :: DBPConf -> Target -> TCM Bool
matchingTarget conf d = maybe (return True) (mutuallyRecursive d) (currentTarget conf)
-}

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

{- | Convert a term (from a dot pattern) to a DeBruijn pattern.
-}

termToDBP :: DBPConf -> Term -> TCM DeBruijnPat
termToDBP conf t
  | not $ useDotPatterns conf = return $ unusedVar
  | otherwise                 = do
    t <- stripAllProjections =<< constructorForm t
    case ignoreSharing t of
      Var i []    -> return $ VarDBP i
      Con c args  -> ConDBP (conName c) <$> mapM (termToDBP conf . unArg) args
      Def s [Apply arg]
        | Just s == withSizeSuc conf -> ConDBP s . (:[]) <$> termToDBP conf (unArg arg)
      Lit l       -> return $ LitDBP l
      _   -> return unusedVar

-- | Removes coconstructors from a deBruijn pattern.
stripCoConstructors :: DBPConf -> DeBruijnPat -> TCM DeBruijnPat
stripCoConstructors conf p = case p of
  VarDBP _  -> return p
  LitDBP _  -> return p
  ProjDBP _ -> return p
  ConDBP c args -> do
    ind <- if withSizeSuc conf == Just c then
             return Inductive
            else
             whatInduction c
    case ind of
      Inductive   -> ConDBP c <$> mapM (stripCoConstructors conf) args
      CoInductive -> return unusedVar

-- | cf. 'TypeChecking.Coverage.Match.buildMPatterns'
openClause :: DBPConf -> Permutation -> [Pattern] -> ClauseBody -> TCM ([DeBruijnPat], Maybe Term)
openClause conf perm ps body = do
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

    build :: Pattern -> StateT [Nat] TCM DeBruijnPat
    build (VarP _)        = VarDBP <$> tick
    build (ConP con _ ps) = ConDBP (conName con) <$> mapM (build . namedArg) ps
    build (DotP t)        = tick *> do lift $ termToDBP conf t
    build (LitP l)        = return $ LitDBP l
    build (ProjP d)       = return $ ProjDBP d

-- | Extract recursive calls from one clause.
termClause :: DBPConf -> MutualNames -> QName -> Delayed -> Clause -> TCM Calls
termClause conf names name delayed clause =
  ifM (isJust <$> isWithFunction name) (return mempty) $
  mapM' (termClause' conf names name delayed) =<< inlineWithClauses name clause

termClause' :: DBPConf -> MutualNames -> QName -> Delayed -> Clause -> TCM Calls
termClause' conf names name delayed clause = do
  cl @ Clause { clauseTel  = tel
              , clausePerm = perm
              , clauseBody = body } <- introHiddenLambdas clause
  let argPats' = clausePats cl
  reportSDoc "term.check.clause" 25 $ vcat
    [ text "termClause"
    , nest 2 $ text "tel      =" <+> prettyTCM tel
    , nest 2 $ text ("perm     = " ++ show perm)
    -- how to get the following right?
    -- , nest 2 $ text "argPats' =" <+> do prettyA =<< reifyPatterns tel perm argPats'
    ]
  addCtxTel tel $ do
    ps <- normalise $ map unArg argPats'
    (dbpats, res) <- openClause conf perm ps body
    case res of
       Nothing -> return Term.empty
       Just t -> do
          dbpats <- mapM (stripCoConstructors conf) dbpats
          termTerm conf names name delayed dbpats t

-- | Rewrite a clause @f ps =tel= \ {xs} -> v@ to @f ps {xs} =(tel {xs})= v@.
--   The pupose is to move hidden bounded size quantifications {j : Size< i}
--   to the lhs such that the termination checker can make use of them.
introHiddenLambdas :: Clause -> TCM Clause
introHiddenLambdas clause@(Clause range ctel perm ps body Nothing)  = return clause
introHiddenLambdas clause@(Clause range ctel perm ps body (Just t)) = do
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

-- | Extract recursive calls from a term.
termTerm :: DBPConf -> MutualNames -> QName -> Delayed -> [DeBruijnPat] -> Term -> TCM Calls
termTerm conf names f delayed pats0 t0 = do
 cutoff <- optTerminationDepth <$> pragmaOptions
 let ?cutoff = cutoff
 do
  reportSDoc "term.check.clause" 6
    (sep [ text ("termination checking " ++
             (if delayed == Delayed then "delayed " else "") ++ "clause of")
           <+> prettyTCM f
         , nest 2 $ text "lhs:" <+> hsep (map prettyTCM pats0)
         , nest 2 $ text "rhs:" <+> prettyTCM t0
         ])
  {-
  -- if we are checking a delayed definition, we treat it as if there were
  -- a guarding coconstructor (sharp)
  let guarded = case delayed of
        Delayed    -> Term.lt
        NotDelayed -> Term.le
  -}
  let guarded = Term.le -- not initially guarded
  loop pats0 guarded t0
  where
       -- only a delayed definition can be guarded
       ifDelayed o | Term.decreasing o && delayed == NotDelayed = Term.le
                   | otherwise                                  = o

       Just fInd = toInteger <$> List.elemIndex f names

       -- sorts can contain arb. terms of type Nat,
       -- so look for recursive calls also
       -- in sorts.  Ideally, Sort would not be its own datatype but just
       -- a subgrammar of Term, then we would not need this boilerplate.
       loopSort :: (?cutoff :: CutOff) => [DeBruijnPat] -> Sort -> TCM Calls
       loopSort pats s = do
         reportSDoc "term.sort" 20 $ text "extracting calls from sort" <+> prettyTCM s
         reportSDoc "term.sort" 50 $ text ("s = " ++ show s)
         -- s <- instantiateFull s -- Andreas, 2012-09-05 NOT NECESSARY
         -- instantiateFull resolves problems with reallyUnLevelView
         -- in the absense of level built-ins.
         -- However, the termination checker should only receive terms
         -- that are already fully instantiated.

         case s of
           Type (Max [])              -> return Term.empty
           Type (Max [ClosedLevel _]) -> return Term.empty
           Type t -> loop pats Term.unknown (Level t) -- no guarded levels
           Prop   -> return Term.empty
           Inf    -> return Term.empty
           DLub s1 (NoAbs x s2) -> Term.union <$> loopSort pats s1 <*> loopSort pats s2
           DLub s1 (Abs x s2)   -> liftM2 Term.union
             (loopSort pats s1)
             (addCtxString x __IMPOSSIBLE__ $ loopSort (map liftDBP pats) s2)

       loopType :: (?cutoff :: CutOff) => [DeBruijnPat] -> Order -> Type -> TCM Calls
       loopType pats guarded (El s t) = liftM2 Term.union
         (loopSort pats s)
         (loop pats guarded t)

       loop
         :: (?cutoff :: CutOff)
         => [DeBruijnPat] -- ^ Parameters of calling function as patterns.
         -> Order         -- ^ Guardedness status of @Term@.
         -> Term          -- ^ Part of function body from which calls are to be extracted.
         -> TCM Calls
       loop pats guarded t = do
         reportSDoc "term.check.term" 50 $ do
           text "looking for calls in" <+> prettyTCM t

         t <- instantiate t          -- instantiate top-level MetaVar

             -- Handles constructor applications.
         let constructor
               :: QName
                  -- ^ Constructor name.
               -> Induction
                  -- ^ Should the constructor be treated as
                  --   inductive or coinductive?
               -> [(I.Arg Term, Bool)]
                  -- ^ All the arguments, and for every
                  --   argument a boolean which is 'True' iff the
                  --   argument should be viewed as preserving
                  --   guardedness.
               -> TCM Calls
             constructor c ind args = mapM' loopArg args
               where
               loopArg (arg , preserves) = do
                 loop pats g' (unArg arg)
                 where g' = case (preserves, ind) of
                              (True,  Inductive)   -> guarded
                              (True,  CoInductive) -> Term.lt .*. guarded
                              (False, _)           -> Term.unknown

             -- Handle guardedness preserving type constructor.
             guardPresTyCon :: QName -> Elims -> (QName -> Elims -> TCM Calls) -> TCM Calls
             guardPresTyCon g es cont
              | guardingTypeConstructors conf = do
                def <- getConstInfo g
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
              | otherwise = cont g es

             withFunction :: QName -> Elims -> TCM Calls
             withFunction g es = do
               v <- expandWithFunctionCall g es
               reportSDoc "term.with.call" 30 $
                 text "termination checking expanded with-function call:" <+> prettyTCM v
               loop pats guarded v

             -- Handles function applications @g args0@.
             function :: QName -> Elims -> TCM Calls
             function g es = do
               isWith <- isWithFunction g
               case isWith of
                 Just f -> withFunction g es
                 Nothing -> do
                   let gArgs = Def g es
                   reportSDoc "term.function" 30 $
                     text "termination checking function call " <+> prettyTCM gArgs
                   -- We have to reduce constructors in case they're reexported.
                   let reduceCon t = case ignoreSharing t of
                          Con c vs -> (`apply` vs) <$> reduce (Con c [])  -- make sure we don't reduce the arguments
                          _        -> return t
                   es <- mapM (etaContract <=< traverse reduceCon <=< instantiateFull) es

                   -- If the function is a projection but not for a coinductive record,
                   -- then preserve guardedness for its principal argument.
                   isProj <- isProjectionButNotCoinductive g
                   let unguards = repeat Term.unknown
                   let guards = if isProj then guarded : unguards
                                               -- proj => preserve guardedness of principal argument
                                          else unguards -- not a proj ==> unguarded
                   -- collect calls in the arguments of this call
                   let args = map unArg $ argsFromElims es
                   calls <- mapM' (uncurry (loop pats)) (zip guards args)

                   reportSDoc "term.found.call" 20
                           (sep [ text "found call from" <+> prettyTCM f
                                , nest 2 $ text "to" <+> prettyTCM g
                                ])

                   -- insert this call into the call list
                   case List.elemIndex g names of

                      -- call leads outside the mutual block and can be ignored
                      Nothing   -> return calls

                      -- call is to one of the mutally recursive functions
                      Just gInd' -> do

                         (nrows, ncols, matrix) <- compareArgs (withSizeSuc conf) pats es
                         reportSLn "term.guardedness" 20 $
                           "composing with guardedness " ++ show guarded ++
                           " counting as " ++ show (ifDelayed guarded)
                         let matrix' = composeGuardedness (ifDelayed guarded) matrix

                         reportSDoc "term.kept.call" 5
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
                         doc <- buildClosure gArgs
                         return
                           (Term.insert
                             (Term.Call { Term.source = fInd
                                        , Term.target = toInteger gInd'
                                        , Term.cm     = makeCM ncols nrows matrix'
                                        })
                             (point
                                (CallInfo { callInfoRange = getRange g
                                          , callInfoCall  = doc
                                          }))
                             calls)


         case ignoreSharing t of

            -- Constructed value.
            Con ConHead{conName = c} args
              | Just c == sharp conf ->
                constructor c CoInductive $ zip args (repeat True)
              | otherwise -> do
                -- If we encounter a coinductive record constructor
                -- in a type mutual with the current target
                -- then we count it as guarding.
                ind <- do
                  r <- isRecordConstructor c
                  case r of
                    Nothing       -> return Inductive
                    Just (q, def) -> return . (\ b -> if b then CoInductive else Inductive) $
                      and [ recRecursive def
                          , recInduction def == CoInductive
                          , targetElem conf (q : recMutual def)
                          ]
                constructor c ind $ zip args (repeat True)

            Def g es -> guardPresTyCon g es function

            -- Abstraction. Preserves guardedness.
            Lam h (Abs x t) -> addCtxString_ x $
              loop (map liftDBP pats) guarded t
            Lam h (NoAbs _ t) -> loop pats guarded t

            -- Neutral term. Destroys guardedness.
            Var i es -> mapM' (loop pats Term.unknown) (map unArg $ argsFromElims es)

            -- Dependent function space.
            Pi a (Abs x b) ->
               do g1 <- loopType pats Term.unknown (unDom a)
                  a  <- maskSizeLt a
                  g2 <- addCtxString x a $
                        loopType (map liftDBP pats) piArgumentGuarded b
                  return $ g1 `Term.union` g2

            -- Non-dependent function space.
            Pi a (NoAbs _ b) ->
               do g1 <- loopType pats Term.unknown (unDom a)
                  g2 <- loopType pats piArgumentGuarded b
                  return $ g1 `Term.union` g2

            -- Literal.
            Lit l -> return Term.empty

            -- Sort.
            Sort s -> loopSort pats s

	    -- Unsolved metas are not considered termination problems, there
	    -- will be a warning for them anyway.
            MetaV x args -> return Term.empty

            -- Erased and not-yet-erased proof.
            DontCare t -> loop pats guarded t

            -- Level.
            Level l -> do
              l <- catchError (reallyUnLevelView l) $ const $ internalError $
                "Termination checker: cannot view level expression, " ++
                "probably due to missing level built-ins."
              loop pats guarded l

            Shared{} -> __IMPOSSIBLE__

         where
         -- Should function and Π type constructors be treated as
         -- preserving guardedness in their right arguments?
         piArgumentGuarded =
           if guardingTypeConstructors conf then
             guarded   -- preserving guardedness
            else
             Term.unknown

-- | Rewrite type @tel -> Size< u@ to @tel -> Size@.
maskSizeLt :: I.Dom Type -> TCM (I.Dom Type)
maskSizeLt dom@(Dom info a) = do
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

{- | compareArgs suc pats ts

     compare a list of de Bruijn patterns (=parameters) @pats@
     with a list of arguments @ts@ and create a call maxtrix
     with |ts| rows and |pats| columns.

     If sized types are enabled, @suc@ is the name of the size successor.

     The guardedness is the number of projection patterns in @pats@
     minus the number of projections in @ts@
 -}
compareArgs ::  (Integral n, ?cutoff :: CutOff) => Maybe QName -> [DeBruijnPat] -> [Elim] -> TCM (n, n, [[Term.Order]])
compareArgs suc pats es = do
  -- matrix <- forM es $ forM pats . compareTerm suc  -- UNREADABLE pointfree style
  matrix <- forM es $ \ e -> forM pats $ \ p -> compareElim suc e p
  -- count the number of coinductive projection(pattern)s in caller and callee
  projsCaller <- genericLength <$> do
    filterM (not <.> isProjectionButNotCoinductive) $ mapMaybe isProjP pats
  projsCallee <- genericLength <$> do
    filterM (not <.> isProjectionButNotCoinductive) $ mapMaybe isProjElim es
  let guardedness = decr $ projsCaller - projsCallee
  reportSLn "term.guardedness" 30 $ "compareArgs: guardedness of call: " ++ show guardedness
  return $ addGuardedness guardedness (size es) (size pats) matrix

-- | @compareElim suc e dbpat@
--   Precondition: top meta variable resolved
compareElim :: (?cutoff :: CutOff) => Maybe QName -> Elim -> DeBruijnPat -> TCM Term.Order
compareElim suc e p = do
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
--    (Proj d, ProjDBP d') | d == d' -> return Term.le
    (Proj d, ProjDBP d')           -> compareProj d d'
    (Proj{}, _         )           -> return Term.unknown
    (Apply{}, ProjDBP{})           -> return Term.unknown
    (Apply arg, p)                 -> compareTerm suc (unArg arg) p

-- | In dependent records, the types of later fields may depend on the
--   values of earlier fields.  Thus when defining an inhabitant of a
--   dependent record type such as Σ by copattern matching,
--   a recursive call eliminated by an earlier projection (proj₁) might
--   occur in the definition at a later projection (proj₂).
--   Thus, earlier projections are considered "smaller" when
--   comparing copattern spines.  This is an ok approximation
--   of the actual dependency order.
--   See issues 906, 942.
compareProj :: QName -> QName -> TCM Term.Order
compareProj d d'
  | d == d' = return Term.le
  | otherwise = do
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
offsetFromConstructor :: QName -> TCM Int
offsetFromConstructor c = maybe 1 (const 0) <$> isRecordConstructor c

-- | Compute the sub patterns of a 'DeBruijnPat'.
subPatterns :: DeBruijnPat -> [DeBruijnPat]
subPatterns p = case p of
  VarDBP _    -> []
  ConDBP c ps -> ps ++ concatMap subPatterns ps
  LitDBP _    -> []
  ProjDBP _   -> []

compareTerm :: (?cutoff :: CutOff) => Maybe QName -> Term -> DeBruijnPat -> TCM Term.Order
compareTerm suc t p = do
--   reportSDoc "term.compare" 25 $
--     text " comparing term " <+> prettyTCM t <+>
--     text " to pattern " <+> prettyTCM p
  t <- stripAllProjections t
  o <- compareTerm' suc t p
  reportSDoc "term.compare" 25 $
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
isProjectionButNotCoinductive :: QName -> TCM Bool
isProjectionButNotCoinductive qn = do
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

-- | compareTerm t dbpat
--   Precondition: top meta variable resolved
compareTerm' :: (?cutoff :: CutOff) => Maybe QName -> Term -> DeBruijnPat -> TCM Term.Order
compareTerm' suc (Shared x)   p = compareTerm' suc (derefPtr x) p
-- Andreas, 2013-11-20 do not drop projections, in any case not coinductive ones!:
compareTerm' suc (Var i es)   p | Just{} <- allApplyElims es
                                = compareVar suc i p
compareTerm' suc (DontCare t) p = compareTerm' suc t p
compareTerm' _ (Lit l)    (LitDBP l')
  | l == l'   = return Term.le
  | otherwise = return Term.unknown
compareTerm' suc (Lit l) p = do
  t <- constructorForm (Lit l)
  case ignoreSharing t of
    Lit _ -> return Term.unknown
    _     -> compareTerm' suc t p
-- Andreas, 2011-04-19 give subterm priority over matrix order
compareTerm' _ t@Con{} (ConDBP c ps)
  | any (isSubTerm t) ps = decrease <$> offsetFromConstructor c <*> return Term.le
compareTerm' suc (Con c ts) (ConDBP c' ps)
  | conName c == c' = compareConArgs suc ts ps
compareTerm' suc (Def s [Apply t]) (ConDBP s' [p])
  | s == s' && Just s == suc = compareTerm' suc (unArg t) p
-- new cases for counting constructors / projections
-- register also increase
compareTerm' suc (Def s [Apply t]) p | Just s == suc = do
    -- Andreas, 2012-10-19 do not cut off here
    increase 1 <$> compareTerm' suc (unArg t) p
compareTerm' suc (Con c []) p = return Term.le
compareTerm' suc (Con c ts) p = do
    increase <$> offsetFromConstructor (conName c)
             <*> (infimum <$> mapM (\ t -> compareTerm' suc (unArg t) p) ts)
compareTerm' suc t p | isSubTerm t p = return Term.le
compareTerm' _ _ _ = return Term.unknown

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

compareConArgs :: (?cutoff :: CutOff) => Maybe QName -> Args -> [DeBruijnPat] -> TCM Term.Order
compareConArgs suc ts ps =
  -- we may assume |ps| >= |ts|, otherwise c ps would be of functional type
  -- which is impossible
      case (length ts, length ps) of
        (0,0) -> return Term.le        -- c <= c
        (0,1) -> return Term.unknown   -- c not<= c x
        (1,0) -> __IMPOSSIBLE__
        (1,1) -> compareTerm' suc (unArg (head ts)) (head ps)
        (_,_) -> foldl (Term..*.) Term.le <$>
                   zipWithM (compareTerm' suc) (map unArg ts) ps
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

compareVar :: (?cutoff :: CutOff) => Maybe QName -> Nat -> DeBruijnPat -> TCM Term.Order
compareVar suc i (VarDBP j)    = compareVarVar suc i j
compareVar suc i (LitDBP _)    = return $ Term.unknown
compareVar suc i (ProjDBP _)   = return $ Term.unknown
compareVar suc i (ConDBP c ps) = do
  decrease <$> offsetFromConstructor c
           <*> (Term.supremum <$> mapM (compareVar suc i) ps)

-- | Compare two variables
compareVarVar :: (?cutoff :: CutOff) => Maybe QName -> Nat -> Nat -> TCM Term.Order
compareVarVar suc i j
  | i == j    = return Term.le
  | otherwise = do
      res <- isBounded i
      case res of
        BoundedNo  -> return Term.unknown
        BoundedLt v -> decrease 1 <$> compareTerm' suc v (VarDBP j)
