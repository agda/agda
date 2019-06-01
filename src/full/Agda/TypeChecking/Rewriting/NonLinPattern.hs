{-# LANGUAGE NondecreasingIndentation #-}
{-# LANGUAGE TypeFamilies #-}

{- | Various utility functions dealing with the non-linear, higher-order
     patterns used for rewrite rules.
-}

module Agda.TypeChecking.Rewriting.NonLinPattern where

import Control.Monad.Reader

import Data.IntSet (IntSet)
import qualified Data.IntSet as IntSet

import Agda.Syntax.Common
import Agda.Syntax.Internal
import Agda.Syntax.Internal.Defs

import Agda.TypeChecking.Datatypes
import Agda.TypeChecking.Free
import Agda.TypeChecking.Free.Lazy
import Agda.TypeChecking.Free.Reduce
import Agda.TypeChecking.Irrelevance (workOnTypes)
import Agda.TypeChecking.Level
import Agda.TypeChecking.Monad
import Agda.TypeChecking.Monad.Builtin
import Agda.TypeChecking.Pretty
import Agda.TypeChecking.Records
import Agda.TypeChecking.Reduce
import Agda.TypeChecking.Substitute
import Agda.TypeChecking.Telescope

import Agda.Utils.Functor
import Agda.Utils.Impossible
import Agda.Utils.List
import Agda.Utils.Maybe
import Agda.Utils.Monad
import Agda.Utils.Null
import Agda.Utils.Singleton
import Agda.Utils.Size

-- | Turn a term into a non-linear pattern, treating the
--   free variables as pattern variables.
--   The first argument indicates the relevance we are working under: if this
--   is Irrelevant, then we construct a pattern that never fails to match.
--   The second argument is the number of bound variables (from pattern lambdas).
--   The third argument is the type of the term.

class PatternFrom t a b where
  patternFrom :: Relevance -> Int -> t -> a -> TCM b

instance (PatternFrom t a b) => PatternFrom (Dom t) (Arg a) (Arg b) where
  patternFrom r k t u = let r' = r `composeRelevance` getRelevance u
                        in  traverse (patternFrom r' k $ unDom t) u

instance PatternFrom (Type, Term) Elims [Elim' NLPat] where
  patternFrom r k (t,hd) = \case
    [] -> return []
    (Apply u : es) -> do
      ~(Pi a b) <- unEl <$> reduce t
      p   <- patternFrom r k a u
      t'  <- t `piApplyM` u
      let hd' = hd `apply` [ u ]
      ps  <- patternFrom r k (t',hd') es
      return $ Apply p : ps
    (IApply x y u : es) -> __IMPOSSIBLE__ -- TODO
    (Proj o f : es) -> do
      ~(Just (El _ (Pi a b))) <- getDefType f =<< reduce t
      let t' = b `absApp` hd
      hd' <- applyDef o f (argFromDom a $> hd)
      ps  <- patternFrom r k (t',hd') es
      return $ Proj o f : ps

instance (PatternFrom t a b) => PatternFrom t (Dom a) (Dom b) where
  patternFrom r k t = traverse $ patternFrom r k t

instance PatternFrom () Type NLPType where
  patternFrom r k _ a = workOnTypes $
    NLPType <$> patternFrom r k () (getSort a)
            <*> patternFrom r k (sort $ getSort a) (unEl a)

instance PatternFrom () Sort NLPat where
  patternFrom r k _ s = do
    s <- reduce s
    let done = return $ PTerm $ Sort s
    case s of
      Type l   -> do
        t <- levelType
        patternFrom Irrelevant k t (Level l)
      Prop l   -> done --TODO
      Inf      -> done
      SizeUniv -> done
      PiSort _ _ -> __IMPOSSIBLE__
      UnivSort _ -> __IMPOSSIBLE__
      MetaS{}  -> __IMPOSSIBLE__
      DefS{}   -> done
      DummyS s -> do
        reportSLn "impossible" 10 $ unlines
          [ "patternFrom: hit dummy sort with content:"
          , s
          ]
        __IMPOSSIBLE__

instance PatternFrom Type Term NLPat where
  patternFrom r k t v = do
    t <- reduce t
    etaRecord <- isEtaRecordType t
    v <- unLevel =<< reduce v
    reportSDoc "rewriting.build" 60 $ sep
      [ "building a pattern from term v = " <+> prettyTCM v
      , " of type " <+> prettyTCM t
      ]
    let done = return $ PTerm v
    case (unEl t , v) of
      (Pi a b , _) -> do
        let body = raise 1 v `apply` [ Arg (domInfo a) $ var 0 ]
        p <- addContext a (patternFrom r (k+1) (absBody b) body)
        return $ PLam (domInfo a) $ Abs (absName b) p
      (_ , Var i es)
       | i < k     -> do
           t <- typeOfBV i
           PBoundVar i <$> patternFrom r k (t , var i) es
       -- The arguments of `var i` should be distinct bound variables
       -- in order to build a Miller pattern
       | Just vs <- allApplyElims es -> do
           TelV tel _ <- telView =<< typeOfBV i
           unless (size tel >= size vs) __IMPOSSIBLE__
           let ts = applySubst (parallelS $ reverse $ map unArg vs) $ map unDom $ flattenTel tel
           mbvs <- forM (zip ts vs) $ \(t , v) -> do
             isEtaVar (unArg v) t >>= \case
               Just j | j < k -> return $ Just $ v $> j
               _              -> return Nothing
           case sequence mbvs of
             Just bvs | fastDistinct bvs -> do
               let allBoundVars = IntSet.fromList (downFrom k)
                   ok = not (isIrrelevant r) ||
                        IntSet.fromList (map unArg bvs) == allBoundVars
               if ok then return (PVar i bvs) else done
             _ -> done
       | otherwise -> done
      (_ , _ ) | Just (d, pars) <- etaRecord -> do
        def <- theDef <$> getConstInfo d
        (tel, c, ci, vs) <- etaExpandRecord_ d pars def v
        caseMaybeM (getFullyAppliedConType c t) __IMPOSSIBLE__ $ \ (_ , ct) -> do
        PDef (conName c) <$> patternFrom r k (ct , Con c ci []) (map Apply vs)
      (_ , Lam i t) -> __IMPOSSIBLE__
      (_ , Lit{})   -> done
      (_ , Def f es) | isIrrelevant r -> done
      (_ , Def f es) -> do
        Def lsuc [] <- primLevelSuc
        Def lmax [] <- primLevelMax
        case es of
          [x]     | f == lsuc -> done
          [x , y] | f == lmax -> done
          _                   -> do
            ft <- defType <$> getConstInfo f
            PDef f <$> patternFrom r k (ft , Def f []) es
      (_ , Con c ci vs) | isIrrelevant r -> done
      (_ , Con c ci vs) ->
        caseMaybeM (getFullyAppliedConType c t) __IMPOSSIBLE__ $ \ (_ , ct) -> do
        PDef (conName c) <$> patternFrom r k (ct , Con c ci []) vs
      (_ , Pi a b) | isIrrelevant r -> done
      (_ , Pi a b) -> do
        pa <- patternFrom r k () a
        pb <- addContext a (patternFrom r (k+1) () $ absBody b)
        return $ PPi pa (Abs (absName b) pb)
      (_ , Sort s)     -> done
      (_ , Level l)    -> __IMPOSSIBLE__
      (_ , DontCare{}) -> done
      (_ , MetaV{})    -> __IMPOSSIBLE__
      (_ , Dummy s _)    -> __IMPOSSIBLE_VERBOSE__ s

-- ^ Convert from a non-linear pattern to a term
class NLPatToTerm p a where
  nlPatToTerm
    :: (MonadReduce m, HasBuiltins m, HasConstInfo m, MonadDebug m)
    => p -> m a
  default nlPatToTerm ::
    ( NLPatToTerm p' a', Traversable f, p ~ f p', a ~ f a'
    , MonadReduce m, HasBuiltins m, HasConstInfo m, MonadDebug m
    ) => p -> m a
  nlPatToTerm = traverse nlPatToTerm

instance NLPatToTerm p a => NLPatToTerm [p] [a] where
instance NLPatToTerm p a => NLPatToTerm (Arg p) (Arg a) where
instance NLPatToTerm p a => NLPatToTerm (Dom p) (Dom a) where
instance NLPatToTerm p a => NLPatToTerm (Elim' p) (Elim' a) where
instance NLPatToTerm p a => NLPatToTerm (Abs p) (Abs a) where

instance NLPatToTerm Nat Term where
  nlPatToTerm = return . var

instance NLPatToTerm NLPat Term where
  nlPatToTerm = \case
    PVar i xs      -> Var i . map Apply <$> nlPatToTerm xs
    PTerm u        -> return u
    PDef f es      -> (theDef <$> getConstInfo f) >>= \case
      Constructor{ conSrcCon = c } -> Con c ConOSystem <$> nlPatToTerm es
      _                            -> Def f <$> nlPatToTerm es
    PLam i u       -> Lam i <$> nlPatToTerm u
    PPi a b        -> Pi <$> nlPatToTerm a <*> nlPatToTerm b
    PBoundVar i es -> Var i <$> nlPatToTerm es

instance NLPatToTerm NLPat Level where
  nlPatToTerm = nlPatToTerm >=> levelView

instance NLPatToTerm NLPType Type where
  nlPatToTerm (NLPType l a) = El <$> (Type <$> nlPatToTerm l) <*> nlPatToTerm a

-- | Gather the set of pattern variables of a non-linear pattern
class NLPatVars a where
  nlPatVarsUnder :: Int -> a -> IntSet

  nlPatVars :: a -> IntSet
  nlPatVars = nlPatVarsUnder 0

instance (Foldable f, NLPatVars a) => NLPatVars (f a) where
  nlPatVarsUnder k = foldMap $ nlPatVarsUnder k

instance NLPatVars NLPType where
  nlPatVarsUnder k (NLPType l a) = nlPatVarsUnder k l `IntSet.union` nlPatVarsUnder k a

instance NLPatVars NLPat where
  nlPatVarsUnder k p =
    case p of
      PVar i _  -> singleton $ i - k
      PDef _ es -> nlPatVarsUnder k es
      PLam _ p' -> nlPatVarsUnder (k+1) $ unAbs p'
      PPi a b   -> nlPatVarsUnder k a `IntSet.union` nlPatVarsUnder (k+1) (unAbs b)
      PBoundVar _ es -> nlPatVarsUnder k es
      PTerm{}   -> empty

-- | Get all symbols that a non-linear pattern matches against
class GetMatchables a where
  getMatchables :: a -> [QName]

  default getMatchables :: (Foldable f, GetMatchables a', a ~ f a') => a -> [QName]
  getMatchables = foldMap getMatchables

instance GetMatchables a => GetMatchables [a] where
instance GetMatchables a => GetMatchables (Arg a) where
instance GetMatchables a => GetMatchables (Dom a) where
instance GetMatchables a => GetMatchables (Elim' a) where
instance GetMatchables a => GetMatchables (Abs a) where

instance (GetMatchables a, GetMatchables b) => GetMatchables (a,b) where
  getMatchables (x,y) = getMatchables x ++ getMatchables y

instance GetMatchables NLPat where
  getMatchables p =
    case p of
      PVar _ _       -> empty
      PDef f _       -> singleton f
      PLam _ x       -> getMatchables x
      PPi a b        -> getMatchables (a,b)
      PBoundVar i es -> getMatchables es
      PTerm u        -> getMatchables u

instance GetMatchables NLPType where
  getMatchables = getMatchables . nlpTypeUnEl

instance GetMatchables Term where
  getMatchables = getDefs' __IMPOSSIBLE__ singleton

instance GetMatchables RewriteRule where
  getMatchables = getMatchables . rewPats

-- Only computes free variables that are not bound (i.e. those in a PTerm)
instance Free NLPat where
  freeVars' p = case p of
    PVar _ _ -> mempty
    PDef _ es -> freeVars' es
    PLam _ u -> freeVars' u
    PPi a b -> freeVars' (a,b)
    PBoundVar _ es -> freeVars' es
    PTerm t -> freeVars' t

instance Free NLPType where
  freeVars' (NLPType l a) =
    ifM ((IgnoreNot ==) <$> asks feIgnoreSorts)
      {- then -} (freeVars' (l, a))
      {- else -} (freeVars' a)
