{-# OPTIONS -fglasgow-exts -cpp #-}

{- Checking for Structural recursion 
   Authors: Andreas Abel, Karl Mehltretter
   Created: 2007-05-28
   Source : TypeCheck.Rules.Decl

 -}

module Termination.TermCheck (termDecls) where

import Control.Monad.Error
import qualified Data.Map as Map
import Data.Map (Map)
import Data.HashTable (hashString)

import qualified Syntax.Abstract as A
import Syntax.Internal
import qualified Syntax.Info as Info
import Syntax.Position
import Syntax.Common
import Syntax.Literal (Literal(LitString))

import Termination.CallGraph
import Termination.Matrix (Size(Size),fromLists)
import Termination.Termination

import TypeChecking.Monad
import TypeChecking.Pretty
import TypeChecking.Reduce (instantiate -- try to get rid of top-level meta-var
                            )
import TypeChecking.Rules.Term (isType_)
import TypeChecking.Substitute (abstract,raise)

import Utils.Size -- "size" 
import Utils.Monad (thread)

-- for __IMPOSSIBLE__
#include "../undefined.h"

type Calls = CallGraph String


-- | Termination check a sequence of declarations.
termDecls :: [A.Declaration] -> TCM ()
termDecls ds = mapM_ termDecl ds

-- | Termination check a single declaration.
termDecl :: A.Declaration -> TCM ()
termDecl d =
    case d of
	A.Axiom i x e		 -> return ()
	A.Primitive i x e	 -> return ()
	A.Definition i ts ds	 -> termMutual i ts ds
	A.Section i x tel ds	 -> termSection i x tel ds
	A.Apply i x m args rd rm -> return ()
	A.Import i x		 -> return ()
	A.Pragma i p		 -> return ()
	A.ScopedDecl scope ds	 -> setScope scope >> termDecls ds
	    -- open is just an artifact from the concrete syntax

collectCalls :: (a -> TCM Calls) -> [a] -> TCM Calls
collectCalls f [] = return emptyCallGraph
collectCalls f (a : as) = do c1 <- f a
                             c2 <- collectCalls f as
                             return (c1 `unionCallGraphs` c2)

-- | Termination check a bunch of mutual inductive recursive definitions.
termMutual :: Info.DeclInfo -> [A.TypeSignature] -> [A.Definition] -> TCM ()
termMutual i ts ds = 
  (do calls <- collectCalls termDefinition ds
      case terminates calls of
        Left  _ -> failed
        Right _ -> when (names /= []) $ reportSLn "term.warn.yes" 2 (show (names) ++ " does termination check"))
  `catchError` \ e -> case e of
                         PatternErr _ -> failed
                         _ -> throwError e
  where getName (A.FunDef i x cs) = [x]
        getName _                 = []
        names = concat (map getName ds)
        failed = reportSLn "term.warn.no" 1 
                   (show (names) ++ " does NOT termination check")

-- | Check an inductive or recursive definition. Assumes the type has has been
--   checked and added to the signature.
termDefinition :: A.Definition -> TCM Calls
termDefinition d =
    case d of
	A.FunDef i x cs	    -> abstract (Info.defAbstract i) $ termFunDef i x cs
	A.DataDef i x ps cs -> return emptyCallGraph
	A.RecDef i x ps cs  -> return emptyCallGraph
    where
	-- Concrete definitions cannot use information about abstract things.
	abstract ConcreteDef = inAbstractMode
	abstract _	     = id

-- | Termination check a module.
termSection :: Info.ModuleInfo -> ModuleName -> A.Telescope -> [A.Declaration] -> TCM ()
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
termFunDef :: Info.DefInfo -> QName -> [A.Clause] -> TCM Calls
termFunDef i name cs =

    traceCall (TermFunDef (getRange i) (qnameName name) cs) $ do   -- TODO!! (qnameName)
	-- Get the type of the function
	t    <- typeOfConst name

	reportSDoc "term.def.fun" 10 $
	  sep [ text "termination checking body of" <+> prettyTCM name
	      , nest 2 $ text ":" <+> prettyTCM t
	      , nest 2 $ text "full type:" <+> (prettyTCM . defType =<< getConstInfo name)
	      ]

	-- Retrieve definition
        def <- getConstInfo name
        -- returns a TC.Monad.Base.Definition
        case (theDef def) of
           Function cls isAbstract -> collectCalls (termClause name) cls
           _ -> __IMPOSSIBLE__

-- | Termination check clauses
{- Invariant: Each clause headed by the same number of patterns

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

{- | stripBind i p b = Just (i', dbp, b')

  i  is the next free de Bruijn level before consumption of ps
  i' is the next free de Bruijn level after  consumption of ps
-}
stripBind :: Nat -> Pattern -> ClauseBody -> Maybe (Nat, DeBruijnPat, ClauseBody)
stripBind _ _ NoBody            = Nothing
stripBind i (VarP x) (NoBind b) = Just (i, unusedVar, b)
stripBind i (VarP x) (Bind (Abs { absName = _, absBody = b })) =
  Just (i+1, VarDBP i, b)
stripBind i (VarP x) (Body b) = __IMPOSSIBLE__
stripBind i (LitP l) b = Just (i, LitDBP l, b)
stripBind i (ConP c args) b 
        = do (i', dbps, b') <- stripBinds i (map unArg args) b 
             return (i', ConDBP c dbps, b')

{- | stripBinds i ps b = Just (i', dbps, b')

  i  is the next free de Bruijn level before consumption of ps
  i' is the next free de Bruijn level after  consumption of ps
-}
stripBinds :: Nat -> [Pattern] -> ClauseBody -> Maybe (Nat, [DeBruijnPat], ClauseBody)
stripBinds i [] b     = return (i, [], b)
stripBinds i (p:ps) b = do (i1,  dbp, b1) <- stripBind i p b
                           (i2, dbps, b2) <- stripBinds i1 ps b1
                           return (i2, dbp:dbps, b2)

termClause :: QName -> Clause -> TCM Calls
termClause name (Clause argPats body) = 
    case stripBinds 0 (map unArg argPats) body  of
       Nothing -> return emptyCallGraph
       Just (n, dbpats, Body t) -> 
          termTerm name (map (adjIndexDBP ((n-1) - )) dbpats) t
          -- note: convert dB levels into dB indices
       Just (n, dbpats, b)  -> internalError $ "termClause: not a Body" -- ++ show b

-- SEVERE HACK: using hashString to convert QName to Index
-- UNSOUND !!
termTerm :: QName -> [DeBruijnPat] -> Term -> TCM Calls
termTerm f pats t = do 
  t' <- instantiate t          -- instantiate top-level MetaVar
  case (ignoreBlocking t') of  -- removes BlockedV case

     -- call to defined function
     Def g args0 -> 
        do let args1 = map unArg args0
           args2 <- mapM instantiate args1
           let args = map ignoreBlocking args2 
           calls <- collectCalls (termTerm f pats) args
           return (insertCallGraph 
                     (Call { source = toInteger (hashString (show f))
                            , target = toInteger (hashString (show g))
                            , callId = show f ++ " --> " ++ show g
                            , cm     = compareArgs pats args
                            })
                     calls)

     -- abstraction
     Lam _ (Abs _ t) -> termTerm f (map liftDBP pats) t

     -- variable
     Var i args -> collectCalls (termTerm f pats) (map unArg args)

     -- constructed value
     Con c args -> collectCalls (termTerm f pats) (map unArg args)

     -- dependent function space
     Pi (Arg _ (El _ a)) (Abs _ (El _ b)) -> 
        do g1 <- termTerm f pats a
           g2 <- termTerm f (map liftDBP pats) b
           return $ unionCallGraphs g1 g2

     -- non-dependent function space
     Fun (Arg _ (El _ a)) (El _ b) -> 
        do g1 <- termTerm f pats a
           g2 <- termTerm f pats b
           return $ unionCallGraphs g1 g2
     
     -- literal
     Lit l -> return emptyCallGraph

     -- sort
     Sort s -> return emptyCallGraph

     -- unsolved meta-variable: violates termination check
     MetaV x args -> patternViolation -- HACK !! abuse of PatternError !!

     BlockedV{} -> __IMPOSSIBLE__

compareArgs :: [DeBruijnPat] -> [Term] -> CallMatrix
compareArgs pats ts 
    = CallMatrix (fromLists (Size (toInteger (length ts)) 
                                  (toInteger (length pats))) 
                   (map (\ t -> map (compareTerm t) pats) ts))

-- | compareTerm t dbpat 
--   Precondition: t not a BlockedV, top meta variable resolved
compareTerm :: Term -> DeBruijnPat -> Order
compareTerm (Var i _) p         = compareVar i p
compareTerm (Lit l) (LitDBP l') = if l==l' then Le else Unknown
compareTerm (Lit l) _           = Unknown
compareTerm (Con c ts) (ConDBP c' ps) 
    = if c == c' then infimum (zipWith compareTerm (map unArg ts) ps)
      else Unknown
compareTerm _ _ = Unknown

compareVar :: Nat -> DeBruijnPat -> Order
compareVar i (VarDBP j) = if i==j then Le else Unknown
compareVar i (LitDBP _) = Unknown
compareVar i (ConDBP c ps) = Lt .*. supremum (map (compareVar i) ps) 



     



