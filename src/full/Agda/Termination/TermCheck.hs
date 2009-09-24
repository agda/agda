{-# LANGUAGE CPP #-}

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
import qualified System.IO.UTF8 as UTF8

import qualified Agda.Syntax.Abstract as A
import Agda.Syntax.Internal
import qualified Agda.Syntax.Info as Info
import Agda.Syntax.Position
import Agda.Syntax.Common
import Agda.Syntax.Literal (Literal(LitString))

import Agda.Termination.CallGraph   as Term
import qualified Agda.Termination.Matrix      as Term
import qualified Agda.Termination.Termination as Term

import Agda.TypeChecking.Monad
import Agda.TypeChecking.Pretty
import Agda.TypeChecking.Reduce (reduce, normalise, instantiate, instantiateFull)
import Agda.TypeChecking.Rules.Term (isType_)
import Agda.TypeChecking.Substitute (abstract,raise,substs)
import Agda.TypeChecking.Telescope
import Agda.TypeChecking.EtaContract
import Agda.TypeChecking.Monad.Builtin
import Agda.TypeChecking.Primitive (constructorForm)

import qualified Agda.Interaction.Highlighting.Range as R
import Agda.Interaction.Options

import Agda.Utils.Size
import Agda.Utils.String
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
termDecl d =
    case d of
	A.Axiom {}		 -> return []
        A.Field {}               -> return []
	A.Primitive {}  	 -> return []
	A.Definition i ts ds	 -> termMutual i ts ds
	A.Section i x tel ds	 -> termSection i x tel ds
	A.Apply {}               -> return []
	A.Import {}		 -> return []
	A.Pragma {}		 -> return []
	A.ScopedDecl scope ds	 -> setScope scope >> termDecls ds
        A.Open {}                -> return []
	    -- open is just an artifact from the concrete syntax

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
     reportSLn "term.top" 20 $ "Termination checking " ++ show names ++ "..."
     mutualBlock <- findMutualBlock (head names)
     let allNames = Set.elems mutualBlock

     -- collect all recursive calls in the block
     let collect use = collectCalls (termDef use allNames) allNames

     -- Get the name of size suc (if sized types are enabled)
     suc <- sizeSuc

     -- first try to termination check ignoring the dot patterns
     let conf = DBPConf { useDotPatterns = False, withSizeSuc = suc }
     calls1 <- collect conf{ useDotPatterns = False }
     reportS "term.lex" 30 $ unlines
       [ "Calls (no dot patterns): " ++ show calls1
       ]
     reportS "term.behaviours" 30 $ unlines
       [ "Recursion behaviours (no dot patterns):"
       , indent 2 $ Term.showBehaviour (Term.complete calls1)
       ]
     r <- do let r = Term.terminates calls1
             case r of
               Right _ -> return r
               Left _  -> do
     -- now try to termination check regarding the dot patterns
                 calls2 <- collect conf{ useDotPatterns = True }
                 reportS "term.lex" 30 $ unlines
                   [ "Calls    (dot patterns): " ++ show calls2
                   ]
                 reportS "term.behaviours" 30 $ unlines
                   [ "Recursion behaviours (no dot patterns):"
                   , indent 2 $ Term.showBehaviour (Term.complete calls1)
                   , "Recursion behaviours (dot patterns):"
                   , indent 2 $ Term.showBehaviour (Term.complete calls2)
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
  getName (A.FunDef i x cs) = [x]
  getName (A.ScopedDef _ d) = getName d
  getName _                 = []

  -- the mutual names mentioned in the abstract syntax
  names = concatMap getName ds

  concat' :: Ord a => [Set a] -> [a]
  concat' = Set.toList . Set.unions

-- | Termination check a module.
termSection :: Info.ModuleInfo -> ModuleName -> A.Telescope -> [A.Declaration] -> TCM Result
termSection i x tel ds =
  termTelescope tel $ \tel' -> do
    addSection x (size tel')
    verboseS "term.section" 10 $ do
      dx   <- prettyTCM x
      dtel <- mapM prettyA tel
      dtel' <- prettyTCM =<< lookupSection x
      liftIO $ UTF8.putStrLn $ "termination checking section " ++ show dx ++ " " ++ show dtel
      liftIO $ UTF8.putStrLn $ "    actual tele: " ++ show dtel'
    withCurrentModule x $ termDecls ds

-- | Termination check a telescope. Binds the variables defined by the telescope.
termTelescope :: A.Telescope -> (Telescope -> TCM a) -> TCM a
termTelescope [] ret = ret EmptyTel
termTelescope (b : tel) ret =
    termTypedBindings b $ \tel1 ->
    termTelescope tel   $ \tel2 ->
	ret $ abstract tel1 tel2


-- | Termination check a typed binding and extends the context with the bound variables.
--   The telescope passed to the continuation is valid in the original context.
termTypedBindings :: A.TypedBindings -> (Telescope -> TCM a) -> TCM a
termTypedBindings (A.TypedBindings i h bs) ret =
    thread (termTypedBinding h) bs $ \bss ->
    ret $ foldr (\(x,t) -> ExtendTel (Arg h t) . Abs x) EmptyTel (concat bss)

termTypedBinding :: Hiding -> A.TypedBinding -> ([(String,Type)] -> TCM a) -> TCM a
termTypedBinding h (A.TBind i xs e) ret = do
    t <- isType_ e
    addCtxs xs (Arg h t) $ ret $ mkTel xs t
    where
	mkTel [] t     = []
	mkTel (x:xs) t = (show $ nameConcrete x,t) : mkTel xs (raise 1 t)
termTypedBinding h (A.TNoBind e) ret = do
    t <- isType_ e
    ret [("_",t)]

-- | Termination check a definition by pattern matching.
termDef :: DBPConf -> MutualNames -> QName -> TCM Calls
termDef use names name = do
	-- Retrieve definition
        def <- getConstInfo name
        -- returns a TC.Monad.Base.Definition

	reportSDoc "term.def.fun" 10 $
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
data DBPConf = DBPConf { useDotPatterns :: Bool
                       , withSizeSuc    :: Maybe QName
                       }

{- | Convert a term (from a dot pattern) to a DeBruijn pattern.
-}

termToDBP :: DBPConf -> Term -> TCM DeBruijnPat
termToDBP conf t
  | not $ useDotPatterns conf = return $ unusedVar
  | otherwise                 = do
    t <- constructorForm t
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
stripBind conf i (ConP c args) b     = do
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
          termTerm names name dbpats t
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
termTerm :: MutualNames -> QName -> [DeBruijnPat] -> Term -> TCM Calls
termTerm names f pats0 t0 = do
  reportSDoc "term.check.clause" 11
    (sep [ text "termination checking clause of" <+> prettyTCM f
         , nest 2 $ text "lhs:" <+> hsep (map prettyTCM pats0)
         , nest 2 $ text "rhs:" <+> prettyTCM t0
         ])
  loop pats0 Le t0
  where
       Just fInd = toInteger <$> List.elemIndex f names
       loop :: [DeBruijnPat] -> Order -> Term -> TCM Calls
       loop pats guarded t = do
         t <- instantiate t          -- instantiate top-level MetaVar
         suc <- sizeSuc
         case t of

            -- call to defined function
            Def g args0 ->
               do let args1 = map unArg args0
                  args2 <- mapM instantiateFull args1

                  -- We have to reduce constructors in case they're reexported.
                  let reduceCon t@(Con _ _) = reduce t
                      reduceCon t           = return t
                  args2 <- mapM reduceCon args2
                  args  <- mapM etaContract args2

                  -- collect calls in the arguments of this call
                  calls <- collectCalls (loop pats Unknown) args


                  reportSDoc "term.found.call" 10
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
                        let ncols   = genericLength pats + 1
                            nrows   = genericLength args + 1
                            matrix' = addGuardedness guarded (ncols - 1) matrix

                        reportSDoc "term.kept.call" 10
                          (sep [ text "kept call from" <+> prettyTCM f
                                  <+> hsep (map prettyTCM pats)
                               , nest 2 $ text "to" <+> prettyTCM g <+>
                                           hsep (map (parens . prettyTCM) args)
                               , nest 2 $ text ("call matrix: " ++ show matrix)
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

            -- abstraction
            Lam _ (Abs _ t) -> loop (map liftDBP pats) guarded t

            -- variable
            Var i args -> collectCalls (loop pats Unknown) (map unArg args)

            -- constructed value
            Con c args -> do
              ind <- whatInduction c
              let g' = case ind of
                        Inductive   -> guarded
                        CoInductive -> Lt .*. guarded
              collectCalls (loop pats g') (map unArg args)

            -- dependent function space
            Pi (Arg _ (El _ a)) (Abs _ (El _ b)) ->
               do g1 <- loop pats guarded a
                  g2 <- loop (map liftDBP pats) guarded b
                  return $ g1 `Term.union` g2

            -- non-dependent function space
            Fun (Arg _ (El _ a)) (El _ b) ->
               do g1 <- loop pats guarded a
                  g2 <- loop pats guarded b
                  return $ g1 `Term.union` g2

            -- literal
            Lit l -> return Term.empty

            -- sort
            Sort s -> return Term.empty

	    -- Unsolved metas are not considered termination problems, there
	    -- will be a warning for them anyway.
            MetaV x args -> return Term.empty

{- | compareArgs suc pats ts

     compare a list of de Bruijn patterns (=parameters) @pats@
     with a list of arguments @ts@ and create a call maxtrix
     with |ts| rows and |pats| columns.

     If sized types are enabled, @suc@ is the name of the size successor.
 -}
compareArgs :: Maybe QName -> [DeBruijnPat] -> [Term] -> TCM [[Term.Order]]
compareArgs suc pats ts = mapM (\t -> mapM (compareTerm suc t) pats) ts

-- | 'makeCM' turns the result of 'compareArgs' into a proper call matrix
makeCM :: Index -> Index -> [[Term.Order]] -> Term.CallMatrix
makeCM ncols nrows matrix = Term.CallMatrix $
  Term.fromLists (Term.Size { Term.rows = nrows
                            , Term.cols = ncols
                            })
                 matrix

-- | 'addGuardedness' adds guardedness flag in the upper left corner (0,0).
addGuardedness :: Integral n => Order -> n -> [[Term.Order]] -> [[Term.Order]]
addGuardedness g ncols m =
  (g : genericReplicate ncols Unknown) : map (Unknown :) m

-- | Compute the sub patterns of a 'DeBruijnPat'.
subPatterns :: DeBruijnPat -> [DeBruijnPat]
subPatterns p = case p of
  VarDBP _    -> []
  ConDBP c ps -> ps ++ concatMap subPatterns ps
  LitDBP _    -> []

compareTerm :: Maybe QName -> Term -> DeBruijnPat -> TCM Term.Order
compareTerm suc t p = compareTerm' suc t p
{-
compareTerm t p = Term.supremum $ compareTerm' t p : map cmp (subPatterns p)
  where
    cmp p' = (Term..*.) Term.Lt (compareTerm' t p')
-}

-- | compareTerm t dbpat
--   Precondition: top meta variable resolved
compareTerm' :: Maybe QName -> Term -> DeBruijnPat -> TCM Term.Order
compareTerm' _ (Var i _)  p              = compareVar i p
compareTerm' _ (Lit l)    (LitDBP l')
  | l == l'   = return Term.Le
  | otherwise = return Term.Unknown
compareTerm' suc (Lit l) p = do
  t <- constructorForm (Lit l)
  case t of
    Lit _ -> return Term.Unknown
    _     -> compareTerm' suc t p
compareTerm' suc (Con c ts) (ConDBP c' ps)
  | c == c' = compareConArgs suc ts ps
compareTerm' suc (Def s ts) (ConDBP s' ps)
  | s == s' && Just s == suc = compareConArgs suc ts ps
compareTerm' _ t@Con{} (ConDBP _ ps)
  | any (isSubTerm t) ps = return Lt
compareTerm' _ _ _ = return Term.Unknown

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

compareConArgs :: Maybe QName -> Args -> [DeBruijnPat] -> TCM Term.Order
compareConArgs suc ts ps =
  -- we may assume |ps| >= |ts|, otherwise c ps would be of functional type
  -- which is impossible
      case (length ts, length ps) of
        (0,0) -> return Term.Le        -- c <= c
        (0,1) -> return Term.Unknown   -- c not<= c x
        (1,0) -> __IMPOSSIBLE__
        (1,1) -> compareTerm' suc (unArg (head ts)) (head ps)
        (_,_) -> do -- build "call matrix"
          m <- mapM (\t -> mapM (compareTerm' suc (unArg t)) ps) ts
          let m2 = makeCM (genericLength ps) (genericLength ts) m
          return $ Term.Mat (Term.mat m2)
{-
--    if null ts then Term.Le
--               else Term.infimum (zipWith compareTerm' (map unArg ts) ps)
     foldl (Term..*.) Term.Le (zipWith compareTerm' (map unArg ts) ps)
       -- corresponds to taking the size, not the height
       -- allows examples like (x, y) < (Succ x, y)
-}

compareVar :: Nat -> DeBruijnPat -> TCM Term.Order
compareVar i (VarDBP j)    = return $ if i == j then Term.Le else Term.Unknown
compareVar i (LitDBP _)    = return $ Term.Unknown
compareVar i (ConDBP c ps) = do
  os <- mapM (compareVar i) ps
  let o = Term.supremum os
  return $ (Term..*.) Term.Lt o
