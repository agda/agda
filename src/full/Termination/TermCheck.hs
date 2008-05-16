{-# LANGUAGE CPP #-}

{- Checking for Structural recursion
   Authors: Andreas Abel, Nils Anders Danielsson, Ulf Norell, 
              Karl Mehltretter and others
   Created: 2007-05-28
   Source : TypeCheck.Rules.Decl
 -}

module Termination.TermCheck (termDecls) where

import Control.Monad.Error
import Data.List as List
import qualified Data.Map as Map
import Data.Map (Map)
import qualified Data.Maybe as Maybe
import qualified Data.Set as Set
import Data.Set (Set)
import Text.PrettyPrint (Doc)

import qualified Syntax.Abstract as A
import Syntax.Internal
import qualified Syntax.Info as Info
import Syntax.Position
import Syntax.Common
import Syntax.Literal (Literal(LitString))

import qualified Termination.CallGraph   as Term
import qualified Termination.Matrix      as Term
import qualified Termination.Termination as Term

import TypeChecking.Monad
import TypeChecking.Monad.Mutual (getMutualBlocks)
import TypeChecking.Pretty
import TypeChecking.Reduce (reduce, instantiate, instantiateFull)
import TypeChecking.Rules.Term (isType_)
import TypeChecking.Substitute (abstract,raise,substs)
import TypeChecking.Telescope

import qualified Interaction.Highlighting.Range as R

import Utils.Size
import Utils.Monad (thread, (<$>))

#include "../undefined.h"
import Utils.Impossible

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
     mutualBlocks <- getMutualBlocks
     -- look for the block containing one of the mutually defined names
     let Just mutualBlock =
           List.find (Set.member (head names)) mutualBlocks
     let allNames = Set.elems mutualBlock
     -- collect all recursive calls in the block
     let collect use = collectCalls (termDef use allNames) allNames
     r <- do r <- Term.terminates <$> collect DontUseDotPatterns
             case r of
               Left _  -> Term.terminates <$> collect UseDotPatterns
               Right _ -> return r
     verboseS "term.lex" 30 $ do
      calls1 <- collect DontUseDotPatterns
      calls2 <- collect UseDotPatterns
      liftIO $ putStrLn $ "Calls (no dot patterns): " ++ show calls1
      liftIO $ putStrLn $ "Calls (dot patterns)   : " ++ show calls2
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
    verbose 10 $ do
      dx   <- prettyTCM x
      dtel <- mapM prettyA tel
      dtel' <- prettyTCM =<< lookupSection x
      liftIO $ putStrLn $ "termination checking section " ++ show dx ++ " " ++ show dtel
      liftIO $ putStrLn $ "    actual tele: " ++ show dtel'
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
termDef :: UseDotPatterns -> MutualNames -> QName -> TCM Calls
termDef use names name = do
	-- Retrieve definition
        def <- getConstInfo name
        -- returns a TC.Monad.Base.Definition

	reportSDoc "term.def.fun" 10 $
	  sep [ text "termination checking body of" <+> prettyTCM name
	      , nest 2 $ text ":" <+> (prettyTCM $ defType def)
	      ]
        case (theDef def) of
           Function cls _ isAbstract -> collectCalls (termClause use names name) cls
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
	         | LitDBP Literal

instance PrettyTCM DeBruijnPat where
  prettyTCM (VarDBP i)    = text $ show i
  prettyTCM (ConDBP c ps) = parens (prettyTCM c <+> hsep (map prettyTCM ps))
  prettyTCM (LitDBP l)    = prettyTCM l 

unusedVar :: DeBruijnPat
unusedVar = LitDBP (LitString noRange "term.unused.pat.var")

adjIndexDBP :: (Nat -> Nat) -> DeBruijnPat -> DeBruijnPat
adjIndexDBP f (VarDBP i) = VarDBP (f i)
adjIndexDBP f (ConDBP c args) = ConDBP c (map (adjIndexDBP f) args)
adjIndexDBP f (LitDBP l) = LitDBP l

{- | liftDeBruijnPat p n

     increases each de Bruijn index in p by n.
     Needed when going under a binder during analysis of a term.
-}

liftDBP :: DeBruijnPat -> DeBruijnPat
liftDBP = adjIndexDBP (1+)

{- | Indicates whether or not to use dot patterns when checking termination.
-}
data UseDotPatterns = UseDotPatterns | DontUseDotPatterns

{- | Convert a term (from a dot pattern) to a DeBruijn pattern.
-}

termToDBP :: UseDotPatterns -> Term -> DeBruijnPat
termToDBP DontUseDotPatterns _ = unusedVar
termToDBP UseDotPatterns     t = case t of
  Var i []    -> VarDBP i
  Con c args  -> ConDBP c $ map (termToDBP UseDotPatterns . unArg) args
  _           -> unusedVar

{- | stripBind i p b = Just (i', dbp, b')

  i  is the next free de Bruijn level before consumption of p
  i' is the next free de Bruijn level after  consumption of p

  if the clause has no body (b = NoBody), Nothing is returned

-}
stripBind :: UseDotPatterns -> Nat -> Pattern -> ClauseBody -> Maybe (Nat, DeBruijnPat, ClauseBody)
stripBind _ _ _ NoBody            = Nothing
stripBind use i (VarP x) (NoBind b) = Just (i, unusedVar, b)
stripBind use i (VarP x) (Bind b)   = Just (i - 1, VarDBP i, absBody b)
stripBind use i (VarP x) (Body b)   = __IMPOSSIBLE__
stripBind use i (DotP t) (NoBind b) = Just (i, termToDBP use t, b)
stripBind use i (DotP t) (Bind b)   = Just (i - 1, termToDBP use t, absBody b)
stripBind use i (DotP _) (Body b)   = __IMPOSSIBLE__
stripBind use i (LitP l) b          = Just (i, LitDBP l, b)
stripBind use i (ConP c args) b     = do 
    (i', dbps, b') <- stripBinds use i (map unArg args) b
    return (i', ConDBP c dbps, b')

{- | stripBinds i ps b = Just (i', dbps, b')

  i  is the next free de Bruijn level before consumption of ps
  i' is the next free de Bruijn level after  consumption of ps
-}
stripBinds :: UseDotPatterns -> Nat -> [Pattern] -> ClauseBody -> Maybe (Nat, [DeBruijnPat], ClauseBody)
stripBinds use i [] b     = return (i, [], b)
stripBinds use i (p:ps) b = do
  (i1,  dbp, b1) <- stripBind use i p b
  (i2, dbps, b2) <- stripBinds use i1 ps b1
  return (i2, dbp:dbps, b2)

-- | Extract recursive calls from one clause.
termClause :: UseDotPatterns -> MutualNames -> QName -> Clause -> TCM Calls
termClause use names name (Clause _ perm argPats' body) =
    case stripBinds use (nVars - 1) (map unArg argPats) body  of
       Nothing -> return Term.empty
       Just (-1, dbpats, Body t) ->
          termTerm names name dbpats t
          -- note: convert dB levels into dB indices
       Just (n, dbpats, Body t) -> internalError $ "termClause: misscalculated number of vars: guess=" ++ show nVars ++ ", real=" ++ show (nVars - 1 - n)
       Just (n, dbpats, b)  -> internalError $ "termClause: not a Body" -- ++ show b
  where
    -- The termination checker doesn't know about reordered telescopes
    argPats = substs (renamingR perm) argPats'
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
  loop pats0 t0
  where 
       Just fInd' = List.elemIndex f names
       fInd = toInteger fInd'
       loop pats t = do
         t' <- instantiate t          -- instantiate top-level MetaVar
         case (ignoreBlocking t') of  -- removes BlockedV case

            -- call to defined function
            Def g args0 ->
               do let args1 = map unArg args0
                  args2 <- mapM instantiateFull args1

                  -- We have to reduce constructors in case they're reexported.
                  let reduceCon t@(Con _ _) = reduce t
                      reduceCon t           = return t
                  args2 <- mapM reduceCon args2
                  let args = map ignoreBlocking args2

                  -- collect calls in the arguments of this call
                  calls <- collectCalls (loop pats) args


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

                        let matrix = compareArgs pats args

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
                                       , Term.cm     = makeCM pats args matrix
                                       })
                            -- Note that only the base part of the
                            -- name is collected here.
                            (Set.fromList $ fst $ R.getRangesA g)
                            calls)

            -- abstraction
            Lam _ (Abs _ t) -> loop (map liftDBP pats) t

            -- variable
            Var i args -> collectCalls (loop pats) (map unArg args)

            -- constructed value
            Con c args -> collectCalls (loop pats) (map unArg args)

            -- dependent function space
            Pi (Arg _ (El _ a)) (Abs _ (El _ b)) ->
               do g1 <- loop pats a
                  g2 <- loop (map liftDBP pats) b
                  return $ g1 `Term.union` g2

            -- non-dependent function space
            Fun (Arg _ (El _ a)) (El _ b) ->
               do g1 <- loop pats a
                  g2 <- loop pats b
                  return $ g1 `Term.union` g2

            -- literal
            Lit l -> return Term.empty

            -- sort
            Sort s -> return Term.empty

	    -- Unsolved metas are not considered termination problems, there
	    -- will be a warning for them anyway.
            MetaV x args -> return Term.empty

            BlockedV{} -> __IMPOSSIBLE__

{- | compareArgs pats ts

     compare a list of de Bruijn patterns (=parameters) @pats@ 
     with a list of arguments @ts@ and create a call maxtrix 
     with |ts| rows and |pats| columns.
 -} 
compareArgs :: [DeBruijnPat] -> [Term] -> [[Term.Order]]
compareArgs pats ts = map (\t -> map (compareTerm t) pats) ts

-- | 'makeCM' turns the result of 'compareArgs' into a proper call matrix
makeCM :: [DeBruijnPat] -> [Term] -> [[Term.Order]] -> Term.CallMatrix
makeCM pats ts matrix = Term.CallMatrix $
  Term.fromLists (Term.Size { Term.rows = toInteger (length ts)
                            , Term.cols = toInteger (length pats)
                            })
                 matrix

-- | Compute the sub patterns of a 'DeBruijnPat'.
subPatterns :: DeBruijnPat -> [DeBruijnPat]
subPatterns p = case p of
  VarDBP _    -> []
  ConDBP c ps -> ps ++ concatMap subPatterns ps
  LitDBP _    -> []

compareTerm :: Term -> DeBruijnPat -> Term.Order
compareTerm = compareTerm'
{-
compareTerm t p = Term.supremum $ compareTerm' t p : map cmp (subPatterns p)
  where
    cmp p' = (Term..*.) Term.Lt (compareTerm' t p')
-}

-- | compareTerm t dbpat
--   Precondition: t not a BlockedV, top meta variable resolved
compareTerm' :: Term -> DeBruijnPat -> Term.Order
compareTerm' (Var i _)  p              = compareVar i p
compareTerm' (Lit l)    (LitDBP l')    = if l == l' then Term.Le
                                                   else Term.Unknown
compareTerm' (Lit l)    _              = Term.Unknown
compareTerm' (Con c ts) (ConDBP c' ps) =
  if c == c' then
  -- we may assume |ps| >= |ts|, otherwise c ps would be of functional type
  -- which is impossible
      case (length ts, length ps) of
        (0,0) -> Term.Le        -- c <= c
        (0,1) -> Term.Unknown   -- c not<= c x
        (1,0) -> __IMPOSSIBLE__ 
        (1,1) -> compareTerm' (unArg (head ts)) (head ps)
        (_,_) -> -- build "call matrix"
          let m =  map (\t -> map (compareTerm' (unArg t)) ps) ts
              m2 = makeCM ps (map unArg ts) m
          in
            Term.Mat (Term.mat m2)
{-
--    if null ts then Term.Le
--               else Term.infimum (zipWith compareTerm' (map unArg ts) ps)
     foldl (Term..*.) Term.Le (zipWith compareTerm' (map unArg ts) ps)
       -- corresponds to taking the size, not the height
       -- allows examples like (x, y) < (Succ x, y)
-}
   else Term.Unknown
compareTerm' _ _ = Term.Unknown

compareVar :: Nat -> DeBruijnPat -> Term.Order
compareVar i (VarDBP j)    = if i == j then Term.Le else Term.Unknown
compareVar i (LitDBP _)    = Term.Unknown
compareVar i (ConDBP c ps) =
  (Term..*.) Term.Lt (Term.supremum (map (compareVar i) ps))
