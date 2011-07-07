{-# LANGUAGE CPP, PatternGuards, ImplicitParams #-}

{- Checking for Structural recursion
   Authors: Andreas Abel, Nils Anders Danielsson, Ulf Norell,
              Karl Mehltretter and others
   Created: 2007-05-28
   Source : TypeCheck.Rules.Decl
 -}

module Agda.Termination.TermCheck
    ( termDecls
    , Result, DeBruijnPat
    ) where

import Control.Monad.Error
import Data.List as List
import qualified Data.Map as Map
import Data.Map (Map)
import qualified Data.Maybe as Maybe
import qualified Data.Set as Set
import Data.Set (Set)
import Text.PrettyPrint (Doc)

import qualified Agda.Syntax.Abstract as A
import Agda.Syntax.Internal
import qualified Agda.Syntax.Info as Info
import Agda.Syntax.Position
import Agda.Syntax.Common
import Agda.Syntax.Literal (Literal(LitString))

import Agda.Termination.CallGraph   as Term
import qualified Agda.Termination.SparseMatrix as Term
import qualified Agda.Termination.Termination  as Term

import Agda.TypeChecking.Monad
import Agda.TypeChecking.Pretty
import Agda.TypeChecking.Reduce (reduce, normalise, instantiate, instantiateFull)
import Agda.TypeChecking.Records (isRecordConstructor)
import Agda.TypeChecking.Rules.Builtin.Coinduction
import Agda.TypeChecking.Rules.Term (isType_)
import Agda.TypeChecking.Substitute (abstract,raise,substs)
import Agda.TypeChecking.Telescope
import Agda.TypeChecking.EtaContract
import Agda.TypeChecking.Monad.Builtin
import Agda.TypeChecking.Monad.Signature (isProjection)
import Agda.TypeChecking.Primitive (constructorForm)
import Agda.TypeChecking.Level (reallyUnLevelView)

import qualified Agda.Interaction.Highlighting.Range as R
import Agda.Interaction.Options

import Agda.Utils.Size
import Agda.Utils.Monad (thread, (<$>), ifM)

#include "../undefined.h"
import Agda.Utils.Impossible

type Calls = Term.CallGraph (Set R.Range)
type MutualNames = [QName]

-- | The result of termination checking a module is a list of
-- problematic mutual blocks (represented by the names of the
-- functions in the block), along with the ranges for the problematic
-- call sites (call site paths).

type Result = [([A.QName], [R.Range])]

-- | Termination check a sequence of declarations.
termDecls :: [A.Declaration] -> TCM Result
termDecls ds = fmap concat $ mapM termDecl ds

-- | Termination check a single declaration.
termDecl :: A.Declaration -> TCM Result
termDecl (A.ScopedDecl scope ds) = do
  setScope scope
  termDecls ds
termDecl d = case d of
    A.Axiom {}            -> return []
    A.Field {}            -> return []
    A.Primitive {}        -> return []
    A.Definition _ _ ds
      | [A.RecDef _ r _ _ _ rds] <- unscopeDefs ds
                          -> do
        let m = mnameFromList $ qnameToList r
        setScopeFromDefs ds
        termSection m rds
    A.Definition i ts ds  -> termMutual i ts ds
    A.Section _ x _ ds    -> termSection x ds
    A.Apply {}            -> return []
    A.Import {}           -> return []
    A.Pragma {}           -> return []
    A.Open {}             -> return []
        -- open is just an artifact from the concrete syntax
    A.ScopedDecl{}        -> __IMPOSSIBLE__
        -- taken care of above
  where
    setScopeFromDefs = mapM_ setScopeFromDef
    setScopeFromDef (A.ScopedDef scope d) =
      setScope scope >> setScopeFromDef d
    setScopeFromDef _ = return ()

    unscopeDefs = concatMap unscopeDef

    unscopeDef (A.ScopedDef _ d) = unscopeDef d
    unscopeDef d = [d]

collectCalls :: (a -> TCM Calls) -> [a] -> TCM Calls
collectCalls f [] = return Term.empty
collectCalls f (a : as) = do c1 <- f a
                             c2 <- collectCalls f as
                             return (c1 `Term.union` c2)

-- | Termination check a bunch of mutually inductive recursive definitions.
termMutual :: Info.DeclInfo -> [A.TypeSignature] -> [A.Definition] -> TCM Result
termMutual i ts ds = if names == [] then return [] else
  do -- get list of sets of mutually defined names from the TCM
     -- this includes local and auxiliary functions introduced
     -- during type-checking

     cutoff <- optTerminationDepth <$> pragmaOptions
     let ?cutoff = cutoff

     reportSLn "term.top" 10 $ "Termination checking " ++ show names ++
       " with cutoff=" ++ show cutoff ++ "..."
     mutualBlock <- findMutualBlock (head names)
     let allNames = Set.elems mutualBlock

     -- collect all recursive calls in the block
     let collect use = collectCalls (termDef use allNames) allNames

     -- Get the name of size suc (if sized types are enabled)
     suc <- sizeSuc

     -- The name of sharp (if available).
     sharp <- fmap nameOfSharp <$> coinductionKit

     guardingTypeConstructors <-
       optGuardingTypeConstructors <$> pragmaOptions

     -- first try to termination check ignoring the dot patterns
     let conf = DBPConf
           { useDotPatterns           = False
           , guardingTypeConstructors = guardingTypeConstructors
           , withSizeSuc              = suc
           , sharp                    = sharp
           }
     calls1 <- collect conf{ useDotPatterns = False }
     reportS "term.lex" 20 $ unlines
       [ "Calls (no dot patterns): " ++ show calls1
       ]
     reportSDoc "term.behaviours" 20 $ vcat
       [ text "Recursion behaviours (no dot patterns):"
       , nest 2 $ return $ Term.prettyBehaviour (Term.complete calls1)
       ]
     reportSDoc "term.matrices" 30 $ vcat
       [ text "Call matrices (no dot patterns):"
       , nest 2 $ pretty $ Term.complete calls1
       ]
     r <- do let r = Term.terminates calls1
             case r of
               Right _ -> return r
               Left _  -> do
                 -- Try again, but include the dot patterns this time.
                 calls2 <- collect conf{ useDotPatterns = True }
                 reportS "term.lex" 20 $ unlines
                   [ "Calls (dot patterns): " ++ show calls2
                   ]
                 reportSDoc "term.behaviours" 20 $ vcat
                   [ text "Recursion behaviours (dot patterns):"
                   , nest 2 $ return $
                       Term.prettyBehaviour (Term.complete calls2)
                   ]
                 reportSDoc "term.matrices" 30 $ vcat
                   [ text "Call matrices (dot patterns):"
                   , nest 2 $ pretty $ Term.complete calls2
                   ]
                 return $ Term.terminates calls2
     case r of
       Left  errDesc -> do
         let callSites = Set.toList errDesc
         return [(names, callSites)] -- TODO: this could be changed to
                                     -- [(allNames, callSites)]
       Right _ -> do
         reportSLn "term.warn.yes" 2
                     (show (names) ++ " does termination check")
         return []
  where
  getName (A.FunDef i x cs)       = [x]
  getName (A.ScopedDef _ d)       = getName d
  getName (A.RecDef _ _ _ _ _ ds) = concatMap getNameD ds
  getName _                       = []

  getNameD (A.Definition _ _ ds) = concatMap getName ds
  getNameD (A.Section _ _ _ ds)  = concatMap getNameD ds
  getNameD (A.ScopedDecl _ ds)   = concatMap getNameD ds
  getNameD _                     = []

  -- the mutual names mentioned in the abstract syntax
  names = concatMap getName ds

  concat' :: Ord a => [Set a] -> [a]
  concat' = Set.toList . Set.unions

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
          Function{ funClauses = cls } ->
            collectCalls (termClause use names name) cls
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

data DeBruijnPat = VarDBP Nat  -- de Bruijn Index
	         | ConDBP QName [DeBruijnPat]
                   -- ^ The name refers to either an ordinary
                   --   constructor or the successor function on sized
                   --   types.
	         | LitDBP Literal

instance PrettyTCM DeBruijnPat where
  prettyTCM (VarDBP i)    = text $ show i
  prettyTCM (ConDBP c ps) = parens (prettyTCM c <+> hsep (map prettyTCM ps))
  prettyTCM (LitDBP l)    = prettyTCM l

unusedVar :: DeBruijnPat
unusedVar = LitDBP (LitString noRange "term.unused.pat.var")

adjIndexDBP :: (Nat -> Nat) -> DeBruijnPat -> DeBruijnPat
adjIndexDBP f (VarDBP i)      = VarDBP (f i)
adjIndexDBP f (ConDBP c args) = ConDBP c (map (adjIndexDBP f) args)
adjIndexDBP f (LitDBP l)      = LitDBP l

{- | liftDeBruijnPat p n

     increases each de Bruijn index in p by n.
     Needed when going under a binder during analysis of a term.
-}

liftDBP :: DeBruijnPat -> DeBruijnPat
liftDBP = adjIndexDBP (1+)

{- | Configuration parameters to termination checker.
-}
data DBPConf = DBPConf { useDotPatterns           :: Bool
                       , guardingTypeConstructors :: Bool
                         -- ^ Do we assume that record and data type
                         --   constructors preserve guardedness?
                       , withSizeSuc              :: Maybe QName
                       , sharp                    :: Maybe QName
                         -- ^ The name of the sharp constructor, if
                         --   any.
                       }

{- | Convert a term (from a dot pattern) to a DeBruijn pattern.
-}

termToDBP :: DBPConf -> Term -> TCM DeBruijnPat
termToDBP conf t
  | not $ useDotPatterns conf = return $ unusedVar
  | otherwise                 = do
    t <- stripProjections =<< constructorForm t
    case t of
      Var i []    -> return $ VarDBP i
      Con c args  -> ConDBP c <$> mapM (termToDBP conf . unArg) args
      Def s [arg]
        | Just s == withSizeSuc conf -> ConDBP s . (:[]) <$> termToDBP conf (unArg arg)
      Lit l       -> return $ LitDBP l
      _   -> return unusedVar

-- | Removes coconstructors from a deBruijn pattern.
stripCoConstructors :: DBPConf -> DeBruijnPat -> TCM DeBruijnPat
stripCoConstructors conf p = case p of
  VarDBP _  -> return p
  LitDBP _ -> return p
  ConDBP c args -> do
    ind <- if withSizeSuc conf == Just c then
             return Inductive
            else
             whatInduction c
    case ind of
      Inductive   -> ConDBP c <$> mapM (stripCoConstructors conf) args
      CoInductive -> return unusedVar

{- | stripBind i p b = Just (i', dbp, b')

  converts a pattern into a de Bruijn pattern

  i  is the next free de Bruijn level before consumption of p
  i' is the next free de Bruijn level after  consumption of p

  if the clause has no body (b = NoBody), Nothing is returned

-}
stripBind :: DBPConf -> Nat -> Pattern -> ClauseBody -> TCM (Maybe (Nat, DeBruijnPat, ClauseBody))
stripBind _ _ _ NoBody            = return Nothing
stripBind conf i (VarP x) (NoBind b) = return $ Just (i, unusedVar, b)
stripBind conf i (VarP x) (Bind b)   = return $ Just (i - 1, VarDBP i, absBody b)
stripBind conf i (VarP x) (Body b)   = __IMPOSSIBLE__
stripBind conf i (DotP t) (NoBind b) = do
  t <- termToDBP conf t
  return $ Just (i, t, b)
stripBind conf i (DotP t) (Bind b)   = do
  t <- termToDBP conf t
  return $ Just (i - 1, t, absBody b)
stripBind conf i (DotP _) (Body b)   = __IMPOSSIBLE__
stripBind conf i (LitP l) b          = return $ Just (i, LitDBP l, b)
stripBind conf i (ConP c _ args) b   = do
    r <- stripBinds conf i (map unArg args) b
    case r of
      Just (i', dbps, b') -> return $ Just (i', ConDBP c dbps, b')
      _                   -> return Nothing

{- | stripBinds i ps b = Just (i', dbps, b')

  i  is the next free de Bruijn level before consumption of ps
  i' is the next free de Bruijn level after  consumption of ps
-}
stripBinds :: DBPConf -> Nat -> [Pattern] -> ClauseBody -> TCM (Maybe (Nat, [DeBruijnPat], ClauseBody))
stripBinds use i [] b     = return $ Just (i, [], b)
stripBinds use i (p:ps) b = do
  r1 <- stripBind use i p b
  case r1 of
    Just (i1, dbp, b1) -> do
      r2 <- stripBinds use i1 ps b1
      case r2 of
        Just (i2, dbps, b2) -> return $ Just (i2, dbp:dbps, b2)
        Nothing -> return Nothing
    Nothing -> return Nothing

-- | Extract recursive calls from one clause.
termClause :: DBPConf -> MutualNames -> QName -> Clause -> TCM Calls
termClause use names name (Clause { clauseTel  = tel
                                  , clausePerm = perm
                                  , clausePats = argPats'
                                  , clauseBody = body }) = do
    argPats' <- addCtxTel tel $ normalise argPats'
    -- The termination checker doesn't know about reordered telescopes
    let argPats = substs (renamingR perm) argPats'
    dbs <- stripBinds use (nVars - 1) (map unArg argPats) body
    case dbs of
       Nothing -> return Term.empty
       Just (-1, dbpats, Body t) -> do
          dbpats <- mapM (stripCoConstructors use) dbpats
          termTerm use names name dbpats t
          -- note: convert dB levels into dB indices
       Just (n, dbpats, Body t) -> internalError $ "termClause: misscalculated number of vars: guess=" ++ show nVars ++ ", real=" ++ show (nVars - 1 - n)
       Just (n, dbpats, b)  -> internalError $ "termClause: not a Body" -- ++ show b
  where
    nVars = boundVars body
    boundVars (Bind b)   = 1 + boundVars (absBody b)
    boundVars (NoBind b) = boundVars b
    boundVars NoBody     = 0
    boundVars (Body _)   = 0

-- | Extract recursive calls from a term.
termTerm :: DBPConf -> MutualNames -> QName -> [DeBruijnPat] -> Term -> TCM Calls
termTerm conf names f pats0 t0 = do
 cutoff <- optTerminationDepth <$> pragmaOptions
 let ?cutoff = cutoff
 do
  reportSDoc "term.check.clause" 6
    (sep [ text "termination checking clause of" <+> prettyTCM f
         , nest 2 $ text "lhs:" <+> hsep (map prettyTCM pats0)
         , nest 2 $ text "rhs:" <+> prettyTCM t0
         ])
  loop pats0 Term.le t0
  where
       Just fInd = toInteger <$> List.elemIndex f names

       -- sorts can contain arb. terms of type Nat,
       -- so look for recursive calls also
       -- in sorts.  Ideally, Sort would not be its own datatype but just
       -- a subgrammar of Term, then we would not need this boilerplate.
       loopSort :: (?cutoff :: Int) => [DeBruijnPat] -> Sort -> TCM Calls
       loopSort pats s = do
         case s of
           Type (Max [])              -> return Term.empty
           Type (Max [ClosedLevel _]) -> return Term.empty
           Type t -> loop pats Term.unknown (Level t)
           Prop   -> return Term.empty
           Inf    -> return Term.empty
           DLub s1 (Abs x s2) -> liftM2 Term.union
             (loopSort pats s1)
             (loopSort (map liftDBP pats) s2)

       loopType :: (?cutoff :: Int) => [DeBruijnPat] -> Order -> Type -> TCM Calls
       loopType pats guarded (El s t) = liftM2 Term.union
         (loopSort pats s)
         (loop pats guarded t)

       loop
         :: (?cutoff :: Int)
         => [DeBruijnPat] -- ^ Parameters of calling function as patterns.
         -> Order         -- ^ Guardedness status of @Term@.
         -> Term          -- ^ Part of function body from which calls are to be extracted.
         -> TCM Calls
       loop pats guarded t = do
         t <- instantiate t          -- instantiate top-level MetaVar
         suc <- sizeSuc

             -- Handles constructor applications.
         let constructor
               :: QName
                  -- ^ Constructor name.
               -> Induction
                  -- ^ Should the constructor be treated as
                  --   inductive or coinductive?
               -> [(Arg Term, Bool)]
                  -- ^ All the arguments, and for every
                  --   argument a boolean which is 'True' iff the
                  --   argument should be viewed as preserving
                  --   guardedness.
               -> TCM Calls
             constructor c ind args = collectCalls loopArg args
               where
               loopArg (arg , preserves) = do
                 loop pats g' (unArg arg)
                 where g' = case (preserves, ind) of
                              (True,  Inductive)   -> guarded
                              (True,  CoInductive) -> Term.lt .*. guarded
                              (False, _)           -> Term.unknown

             -- Handles function applications @g args0@.
             function :: QName -> [Arg Term] -> TCM Calls
             function g args0 = do
               let args1 = map unArg args0
               args2 <- mapM instantiateFull args1

               -- We have to reduce constructors in case they're reexported.
               let reduceCon t@(Con _ _) = reduce t
                   reduceCon t           = return t
               args2 <- mapM reduceCon args2
               args  <- mapM etaContract args2

               -- If the function is a projection, then preserve guardedness
               -- for its principal argument.
               isProj <- isProjection g
               let unguards = repeat Term.unknown
               let guards = maybe unguards -- not a proj. ==> unguarded
                              (\ n -> take (n - 1) unguards ++ guarded : unguards)
                                -- proj. => preserve g. of princ. arg. (counting starts with 1)
                              isProj
               -- collect calls in the arguments of this call
               calls <- collectCalls (uncurry (loop pats)) (zip guards args)
               -- calls <- collectCalls (loop pats Term.unknown) args


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

                     matrix <- compareArgs suc pats args
                     let (nrows, ncols, matrix') = addGuardedness guarded
                            (genericLength args) -- number of rows
                            (genericLength pats) -- number of cols
                            matrix


                     reportSDoc "term.kept.call" 5
                       (sep [ text "kept call from" <+> prettyTCM f
                               <+> hsep (map prettyTCM pats)
                            , nest 2 $ text "to" <+> prettyTCM g <+>
                                        hsep (map (parens . prettyTCM) args)
                            , nest 2 $ text ("call matrix (with guardeness): " ++ show matrix')
                            ])

                     return
                       (Term.insert
                         (Term.Call { Term.source = fInd
                                    , Term.target = toInteger gInd'
                                    , Term.cm     = makeCM ncols nrows matrix'
                                    })
                         -- Note that only the base part of the
                         -- name is collected here.
                         (Set.fromList $ fst $ R.getRangesA g)
                         calls)


         case t of

            -- Constructed value.
            Con c args ->
              constructor c Inductive $ zip args (repeat True)

            Def g args0
              | Just g == sharp conf ->
                constructor g CoInductive $ zip args0 (repeat True)
              | guardingTypeConstructors conf -> do
                gDef <- theDef <$> getConstInfo g
                case gDef of
                  Datatype {dataArgOccurrences = occs} -> con occs
                  Record   {recArgOccurrences  = occs} -> con occs
                  _                                    -> fun
              | otherwise -> fun
              where
              -- Data or record type constructor.
              con occs =
                constructor g Inductive $   -- guardedness preserving
                -- constructor g CoInductive $ -- guarding! (Andreas, 2011-04-10) -- does not work, might lead to infinite unfolding in eq. checking (Ripley!)
                  zip args0 (map preserves occs ++ repeat False)
                where
                preserves Positive = True
                preserves Negative = False
                preserves Unused   = True

              -- Call to defined function.
              fun = function g args0

            -- Abstraction. Preserves guardedness.
            Lam h (Abs x t) -> loop (map liftDBP pats) guarded t

            -- Neutral term. Destroys guardedness.
            Var i args -> collectCalls (loop pats Term.unknown) (map unArg args)

            -- Dependent function space.
            Pi a (Abs _ b) ->
               do g1 <- loopType pats Term.unknown (unArg a)
                  g2 <- loopType (map liftDBP pats) piArgumentGuarded b
                  return $ g1 `Term.union` g2

            -- Non-dependent function space.
            Fun a b ->
               do g1 <- loopType pats Term.unknown (unArg a)
                  g2 <- loopType pats piArgumentGuarded b
                  return $ g1 `Term.union` g2

            -- Literal.
            Lit l -> return Term.empty

            -- Sort.
            Sort s -> loopSort pats s

	    -- Unsolved metas are not considered termination problems, there
	    -- will be a warning for them anyway.
            MetaV x args -> return Term.empty

            -- Erased proof.
            DontCare -> return Term.empty

            -- Level
            Level l -> loop pats guarded =<< reallyUnLevelView l

         where
         -- Should function and Π type constructors be treated as
         -- preserving guardedness in their right arguments?
         piArgumentGuarded =
           if guardingTypeConstructors conf then
             guarded   -- preserving guardedness
             -- Term.lt      -- guarding! (Andreas, 2011-04-10)  -- SEE ABOVE
            else
             Term.unknown

{- | compareArgs suc pats ts

     compare a list of de Bruijn patterns (=parameters) @pats@
     with a list of arguments @ts@ and create a call maxtrix
     with |ts| rows and |pats| columns.

     If sized types are enabled, @suc@ is the name of the size successor.
 -}
compareArgs ::  (?cutoff :: Int) => Maybe QName -> [DeBruijnPat] -> [Term] -> TCM [[Term.Order]]
compareArgs suc pats ts = mapM (\t -> mapM (compareTerm suc t) pats) ts

-- | 'makeCM' turns the result of 'compareArgs' into a proper call matrix
makeCM :: Index -> Index -> [[Term.Order]] -> Term.CallMatrix
makeCM ncols nrows matrix = Term.CallMatrix $
  Term.fromLists (Term.Size { Term.rows = nrows
                            , Term.cols = ncols
                            })
                 matrix

{- To turn off guardedness, restore this code.
-- | 'addGuardedness' does nothing.
addGuardedness :: Integral n => Order -> n -> n -> [[Term.Order]] -> (n, n, [[Term.Order]])
addGuardedness g nrows ncols m = (nrows, ncols, m)
-}

-- | 'addGuardedness' adds guardedness flag in the upper left corner (0,0).
addGuardedness :: Integral n => Order -> n -> n -> [[Term.Order]] -> (n, n, [[Term.Order]])
addGuardedness g nrows ncols m =
  (nrows + 1, ncols + 1,
   (g : genericReplicate ncols Term.unknown) : map (Term.unknown :) m)

-- | Stripping off a record constructor is not counted as decrease, in
--   contrast to a data constructor.
decreaseFromConstructor :: QName -> TCM Order
decreaseFromConstructor c = do
  isRC <- isRecordConstructor c
  return $ if isRC then Term.le else Term.lt

increaseFromConstructor :: (?cutoff :: Int) => QName -> TCM Order
increaseFromConstructor c = do
  isRC <- isRecordConstructor c
  return $ if isRC then Term.le else Term.decr (-1)

{-
increaseFromConstructor c = negateOrder <$> decreaseFromConstructor c
  where negateOrder (Decr k) = Decr (- k)
        negateOrder _ = __IMPOSSIBLE__
-}

-- | Compute the sub patterns of a 'DeBruijnPat'.
subPatterns :: DeBruijnPat -> [DeBruijnPat]
subPatterns p = case p of
  VarDBP _    -> []
  ConDBP c ps -> ps ++ concatMap subPatterns ps
  LitDBP _    -> []

compareTerm :: (?cutoff :: Int) => Maybe QName -> Term -> DeBruijnPat -> TCM Term.Order
compareTerm suc t p = do
  t <- stripAllProjections t
  compareTerm' suc t p

{-
compareTerm t p = Term.supremum $ compareTerm' t p : map cmp (subPatterns p)
  where
    cmp p' = (Term..*.) Term.lt (compareTerm' t p')
-}

-- | Remove projections until a term is no longer a projection.
stripProjections :: Term -> TCM Term
stripProjections t@(Def qn ts) = do
  isProj <- isProjection qn
  case isProj of
    Just n | length ts >= n, n >= 1 -> stripProjections $ unArg $ ts !! (n - 1)
    _ -> return t
stripProjections t = return t

-- | Remove all projections from an algebraic term (not going under binders).
class StripAllProjections a where
  stripAllProjections :: a -> TCM a

instance StripAllProjections a => StripAllProjections (Arg a) where
  stripAllProjections (Arg h r a) = Arg h r <$> stripAllProjections a

instance StripAllProjections a => StripAllProjections [a] where
  stripAllProjections = mapM stripAllProjections

instance StripAllProjections Term where
  stripAllProjections t = do
    t <- stripProjections t
    case t of
      Con c ts -> Con c <$> stripAllProjections ts
      Def d ts -> Def d <$> stripAllProjections ts
      _ -> return t

{-
-- | Remove all projections from an algebraic term (not going under binders).
stripAllProjections :: Term -> TCM Term
stripAllProjections t = do
  t <- stripProjections t
  case t of
    Con c ts -> Con c <$> mapM stripAllProjections ts
    Def d ts -> Def d <$> mapM stripAllProjections ts
    _ -> return t
-}

-- | compareTerm t dbpat
--   Precondition: top meta variable resolved
compareTerm' :: (?cutoff :: Int) => Maybe QName -> Term -> DeBruijnPat -> TCM Term.Order
compareTerm' _ (Var i _)  p              = compareVar i p
compareTerm' _ (Lit l)    (LitDBP l')
  | l == l'   = return Term.le
  | otherwise = return Term.unknown
compareTerm' suc (Lit l) p = do
  t <- constructorForm (Lit l)
  case t of
    Lit _ -> return Term.unknown
    _     -> compareTerm' suc t p
-- Andreas, 2011-04-19 give subterm priority over matrix order
compareTerm' _ t@Con{} (ConDBP c ps)
  | any (isSubTerm t) ps = decreaseFromConstructor c
compareTerm' suc (Con c ts) (ConDBP c' ps)
  | c == c' = compareConArgs suc ts ps
compareTerm' suc (Def s ts) (ConDBP s' ps)
  | s == s' && Just s == suc = compareConArgs suc ts ps
-- new cases for counting constructors / projections
-- register also increase
compareTerm' suc (Def s ts) p | Just s == suc = do
    os <- mapM (\ t -> compareTerm' suc (unArg t) p) ts
    return $ decr (-1) .*. infimum os
{- Andreas 2011-07-07 Projections are now being removed in a preprocess
-- projections are size preserving
compareTerm' suc (Def qn ts) p = do
    isProj <- isProjection qn
    case isProj of
      -- strip off projection (n is the number of the record argument, counting starts with 1)
      Just n | length ts >= n && n >= 1 ->
        compareTerm' suc (unArg (ts !! (n - 1))) p
      -- not a projection or underapplied:
      _ -> return Term.unknown
-}
compareTerm' suc (Con c ts) p = do
    os <- mapM (\ t -> compareTerm' suc (unArg t) p) ts
    oc <- increaseFromConstructor c
    return $ if (null os) then Term.unknown else oc .*. infimum os
compareTerm' suc t p | isSubTerm t p = return Term.le
compareTerm' _ _ _ = return Term.unknown

-- TODO: isSubTerm should compute a size difference (Term.Order)
isSubTerm :: Term -> DeBruijnPat -> Bool
isSubTerm t p = equal t p || properSubTerm t p
  where
    equal (Con c ts) (ConDBP c' ps) =
      and $ (c == c')
          : (length ts == length ps)
          : zipWith equal (map unArg ts) ps
    equal (Var i []) (VarDBP j) = i == j
    equal (Lit l) (LitDBP l') = l == l'
    equal _ _ = False

    properSubTerm t (ConDBP _ ps) = any (isSubTerm t) ps
    properSubTerm _ _ = False

compareConArgs :: (?cutoff :: Int) => Maybe QName -> Args -> [DeBruijnPat] -> TCM Term.Order
compareConArgs suc ts ps =
  -- we may assume |ps| >= |ts|, otherwise c ps would be of functional type
  -- which is impossible
      case (length ts, length ps) of
        (0,0) -> return Term.le        -- c <= c
        (0,1) -> return Term.unknown   -- c not<= c x
        (1,0) -> __IMPOSSIBLE__
        (1,1) -> compareTerm' suc (unArg (head ts)) (head ps)
        (_,_) -> do -- build "call matrix"
          m <- mapM (\t -> mapM (compareTerm' suc (unArg t)) ps) ts
          let m2 = makeCM (genericLength ps) (genericLength ts) m
          return $ Term.orderMat (Term.mat m2)
{-
--    if null ts then Term.Le
--               else Term.infimum (zipWith compareTerm' (map unArg ts) ps)
     foldl (Term..*.) Term.Le (zipWith compareTerm' (map unArg ts) ps)
       -- corresponds to taking the size, not the height
       -- allows examples like (x, y) < (Succ x, y)
-}

compareVar :: (?cutoff :: Int) => Nat -> DeBruijnPat -> TCM Term.Order
compareVar i (VarDBP j)    = return $ if i == j then Term.le else Term.unknown
compareVar i (LitDBP _)    = return $ Term.unknown
compareVar i (ConDBP c ps) = do
  os <- mapM (compareVar i) ps
  let o = Term.supremum os
  oc <- decreaseFromConstructor c
  return $ (Term..*.) oc o
