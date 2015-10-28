{-# LANGUAGE CPP               #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE PatternGuards     #-}

module Agda.Compiler.Epic.Injection where

import Control.Monad.State
import Control.Monad.Reader

import Data.IntMap (IntMap)
import qualified Data.IntMap as IntMap
import Data.List
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Maybe
import Data.Set (Set)
import qualified Data.Set as Set

import Agda.Syntax.Common
import Agda.Syntax.Internal as I
import Agda.Syntax.Internal.Pattern (FunArity(..), unnumberPatVars)
import Agda.Syntax.Literal
import Agda.TypeChecking.CompiledClause
import Agda.TypeChecking.Monad
import Agda.TypeChecking.Monad.Builtin
import Agda.TypeChecking.Pretty
import Agda.TypeChecking.Reduce
import Agda.TypeChecking.Substitute
import Agda.Utils.List
import Agda.Utils.Monad
import Agda.Utils.Null

import Agda.Compiler.Epic.CompileState
import Agda.Compiler.Epic.Interface as Interface

#include "undefined.h"
import Agda.Utils.Impossible
import Agda.Utils.Lens

-- | Find potentially injective functions, solve constraints to fix some constructor
--   tags and make functions whose constraints are fulfilled injections
findInjection :: [(QName, Definition)] -> Compile TCM [(QName, Definition)]
findInjection defs = do
    funs <- forM defs $ \(name, def) -> case theDef def of
        f@(Function{}) -> isInjective name (funClauses f)
        _              -> return Nothing
    newNames <- Map.keys <$> gets (Interface.conArity . curModule)
    injFuns <- solve newNames (catMaybes funs)
    defs' <- forM defs $ \(q, def) -> case q `isIn` injFuns of
        Nothing -> return (q, def)
        Just inj@(InjectiveFun nvar arity) -> case theDef def of
            f@(Function{})   -> do
                modifyEI $ \s -> s { injectiveFuns = Map.insert q inj (injectiveFuns s) }
                let ns = replicate arity (defaultArg empty)
                return $ (,) q $ def { theDef = f { funCompiled = Just $ Done ns $
                                                      var $ arity - nvar - 1 } }
            _                -> __IMPOSSIBLE__

    lift $ reportSLn "epic.injection" 10 $ "injfuns: " ++ show injFuns
    return defs'
  where
    q `isIn` funs = case filter (\(nam, _) -> q == nam) funs of
        []   -> Nothing
        (_,x):_  -> Just x

replaceFunCC :: QName -> CompiledClauses -> Compile TCM ()
replaceFunCC name cc = lift $ do
    stSignature %= updateDefinition name replaceDef
    stImports   %= updateDefinition name replaceDef
  where
    replaceDef :: Definition -> Definition
    replaceDef def = case theDef def of
        f@(Function{}) -> def {theDef = f { funCompiled = Just $ cc } }
        x                -> __IMPOSSIBLE__

-- | If the pairs of constructor names have the same tags, the function is
--   injective. If Nothing, the function is not injective.
type InjConstraints = Maybe [(QName,QName)]


isInjective :: QName    -- ^ Name of the function being tested
            -> [Clause] -- ^ The function's clauses
            -> Compile TCM (Maybe ((QName, InjectiveFun)
                                  , [(QName, QName)] -- These construtors should have the same name
                                  ))
isInjective nam []  = return Nothing
isInjective nam cls@(cl : _) = do
    lift $ reportSLn "epic.injection" 20 $ "checking isInjective " ++ show nam
    let total = funArity cls
    (listToMaybe . catMaybes <$>) . forM [0 .. total - 1] $ \i -> do
        cli <- forM cls $ \ cl -> isInjectiveHere nam i  cl
        let cli' = catMaybes cli
        return $ if length cli == length cli'
             then Just ((nam, InjectiveFun i total), concat cli')
             else Nothing

patternToTerm :: Nat -> Pattern -> Term
patternToTerm n p = case p of
    VarP v          -> var n
    DotP t          -> t
    ConP c typ args -> Con c $ zipWith (\ arg t -> arg {unArg = t}) args
                             $ snd
                             $ foldr (\ arg (n, ts) -> (n + nrBinds arg, patternToTerm n arg : ts))
                                     (n , [])
                             $ map namedArg args
    LitP l          -> Lit l
    ProjP d         -> Def d [] -- Andreas, 2012-10-31 that might not be enought to get a term from list of patterns (TODO)

nrBinds :: Num i => Pattern -> i
nrBinds p = case p of
    VarP v          -> 1
    DotP t          -> 0
    ConP c typ args -> sum $ map (nrBinds . namedArg) args
    LitP l          -> 0
    ProjP{}         -> 0

substForDot :: [NamedArg (Pattern' a)] -> Substitution
substForDot = makeSubst 0 0 . reverse . calcDots
  where
    makeSubst i accum [] = raiseS (i + accum)
    makeSubst i accum (True  : ps) = makeSubst i (accum +1) ps
    makeSubst i accum (False : ps) = consS (var $ i + accum) $ makeSubst (i+1) accum ps

    calcDots = concatMap calcDots' . map namedArg
    calcDots' p = case p of
        VarP v          -> [False]
        DotP t          -> [True]
        ConP c typ args -> calcDots args
        LitP l          -> [False]
        ProjP{}         -> [False]

isInjectiveHere :: QName  -- ^ Name of the function being tested
                -> Int    -- ^ The current argument
                -> Clause
                -> Compile TCM InjConstraints
isInjectiveHere nam idx clause = do
 lift $ reportSDoc "epic.injection" 40 $ sep
   [ text "isInjectiveHere"
   , prettyTCM nam
   , text ("argumentNo=" ++ show idx)
   -- , prettyTCM (clausePats clause)
   ]
 case getBody clause of
  Nothing -> return emptyC
  Just body -> do
    let t    = patternToTerm idxR $ unArg $ fromMaybe __IMPOSSIBLE__ $
                 unnumberPatVars (clausePats clause) !!! idx
        t'   = applySubst (substForDot $ namedClausePats clause) t
        idxR = sum . map (nrBinds . unArg) . genericDrop (idx + 1) $ unnumberPatVars $ clausePats clause
    body' <- lift $ reduce body
    lift $ reportSLn "epic.injection" 40 "reduced body"
    injFs <- gets (injectiveFuns . importedModules)
    lift $ reportSLn "epic.injection" 40 "calculated injFs"
    res <- (t' <: body') `runReaderT` (Map.insert nam (InjectiveFun idx
                                                      (length (clausePats clause))) injFs)
    lift $ reportSDoc "epic.injection" 20 $ vcat
      [ text "isInjective:" <+> text (show nam)
      , text "at Index   :" <+> text (show idx)
      , nest 2 $ vcat
          [ text "clause     :" <+> text (show clause)
          , text "t          :" <+> prettyTCM t
          , text "idxR       :" <+> (text . show) idxR
          , text "body'      :" <+> (text . show) body'
          ]
      , text "res      :" <+> text (show res)
      ]
    return res

-- | Turn NATURAL literal n into suc^n zero.
litToCon :: Literal -> TCM Term
litToCon l = case l of
    LitNat   r n | n > 0     -> do
        inner <- litToCon (LitNat r (n - 1))
        suc   <- primSuc
        return $ suc `apply` [defaultArg inner]
                 | otherwise -> primZero
--    LitLevel _ n -> -- Does not really matter
    lit          -> return $ Lit lit

litInt :: Literal -> Bool
litInt LitNat{} = True
litInt _        = False

insertAt :: (Nat,Term) -> Term -> Term
insertAt (index, ins) = applySubst $
  [var i | i <- [0 .. index - 1]] ++# consS ins (raiseS $ index + 1)

solve :: [QName] -> [((QName, InjectiveFun), [(QName,QName)])] -> Compile TCM [(QName, InjectiveFun)]
solve newNames xs = do
    lift $ reportSDoc "epic.injection" 30 $
      sep $ text "Epic.Injection.solve" : map prettyTCM newNames
    -- Only primitive lists should be in the current module at this point,
    -- but we still want them
    conGraph <- Map.union <$> gets (constrTags . curModule) <*> gets (constrTags . importedModules)
    (funs, mconstr) <- ($ xs) $ flip foldM ([] , Just $ initialTags conGraph newNames) $ \ (xs , prev) (fun , con) -> do
         m <- foldM solvable prev con
         return $ case m of
            Nothing -> (xs, prev)
            Just next -> (fun : xs, m)
    case mconstr of
        Nothing -> __IMPOSSIBLE__
        Just constr -> updateTags constr
    return funs
  where
    solvable :: Maybe Tags -> (QName, QName)
             -> Compile TCM (Maybe Tags)
    solvable Nothing _          = return Nothing
    solvable (Just st) (c1, c2) = unify c1 c2 st

    updateTags :: Tags -> Compile TCM ()
    updateTags tags = do
        let (hasTags, eqs) = Map.partition isTag (constrGroup tags)
            isTag (IsTag _) = True
            isTag _         = False
        forM_ (Map.toList hasTags) $ \ (c, tagged) -> case tagged of
            IsTag tag -> putCon c tag
            _         -> __IMPOSSIBLE__
        case Map.toList eqs of
            (c, Same n) : _ -> do
                let grp = fromMaybe __IMPOSSIBLE__ $ IntMap.lookup n $ eqGroups tags
                tag <- assignConstrTag' c (Set.toList grp)
                updateTags . fromMaybe __IMPOSSIBLE__ =<< setTag n tag tags { constrGroup = eqs }
            _              -> return ()
    putCon :: QName -> Tag -> Compile TCM ()
    putCon con tag = do
        m <- gets (constrTags . importedModules)
        case Map.lookup con m of
            Nothing -> putConstrTag con tag
            Just _  -> return () -- old

emptyC :: InjConstraints
emptyC = Just []

addConstraint :: QName -> QName -> InjConstraints -> InjConstraints
addConstraint q1 q2 Nothing   = Nothing
addConstraint q1 q2 (Just xs) = Just (if q1 == q2 then xs else (q1,q2) : xs)

unionConstraints :: [InjConstraints] -> InjConstraints
unionConstraints [] = Just []
unionConstraints (Nothing : _) = Nothing
unionConstraints (Just c : cs) = do
    cs' <- unionConstraints cs
    return (c ++ cs')

-- | Are two terms injectible?
--   Tries to find a mapping between constructors that equates the terms.
--
--   Precondition: t1 is normalised, t2 is in WHNF
-- When reducing t2, it may become a literal, which makes this not work in some cases...
class Injectible a where
  (<:) :: a -> a -> ReaderT (Map QName InjectiveFun) (Compile TCM) InjConstraints

instance Injectible a => Injectible (Arg a) where
  a1 <: a2 = unArg a1 <: unArg a2

instance Injectible a => Injectible [a] where
  l1 <: l2
    | length l1 == length l2 = unionConstraints <$> zipWithM (<:) l1 l2
    | otherwise              = return Nothing

instance Injectible a => Injectible (Elim' a) where
  e1 <: e2 =
    case (e1, e2) of
      (Proj f1 , Proj f2 ) | f1 == f2 -> return $ Just []
      (Apply a1, Apply a2)            -> a1 <: a2
      _                               -> return Nothing

instance Injectible Term where
  t1 <: t2 = do
    injs <- ask
    -- Andreas, 2013-10-18: ignoring the precondition (NF, WHNF) since I am not maintaining it
    -- in recursive calls.
    -- The original code did not follow this invariant in the Var-Var and Def-Def case,
    -- thus, I am not trusting it.  Also the call site does not seem to ensure it.
    -- It could be restored by only reducing the right argument in the Arg-instance.

    -- (t1, t2) <- lift . lift . reduce $ (t1, t2)  -- NOTE: reduce *introduces* Lit! Loops!
    case (ignoreSharing t1, ignoreSharing t2) of
      (Lit l, Lit l') | l == l' -> return $ Just []
      (Lit l, _) | litInt l -> do
        l' <- lift . lift $ litToCon l
        l' <: t2
      (_,  Lit l) | litInt l -> do
        l' <- lift . lift $ litToCon l
        t1 <: l'
      (_, Def n2 es2) | Just (InjectiveFun argn arit) <- Map.lookup n2 injs -> do
        if genericLength es2 /= arit
          then return Nothing
          else do
            case es2 !!! argn of
              Nothing        -> __IMPOSSIBLE__
              Just (Proj{})  -> __IMPOSSIBLE__
              Just (Apply a) -> t1 <: unArg a
      (Var i1 es1, Var i2 es2) | i1 == i2 -> es1 <: es2
      (Def q1 es1, Def q2 es2) | q1 == q2 -> es1 <: es2
      (Con con1 args1, Con con2 args2) -> do
        let c1 = conName con1
            c2 = conName con2
        args1' <- flip notForced args1 <$> do lift . getForcedArgs $ c1
        args2' <- flip notForced args2 <$> do lift . getForcedArgs $ c2
        addConstraint c1 c2 <$> do
          args1' <: args2'
      _ -> return Nothing
{-
      (_, Def n2 args2) | Just (InjectiveFun argn arit) <- Map.lookup n2 injs -> do
        if genericLength args2 /= arit
          then return Nothing
          else do
              arg <- lift . lift . reduce $ unArg $ args2 !! argn
              t1 <: arg
      (Var n1 args1, Var n2 args2) | n1 == n2 && length args1 == length args2 -> do
        args1' <- map unArg <$> mapM (lift . lift . reduce) args1
        args2' <- map unArg <$> mapM (lift . lift . reduce) args2
        unionConstraints <$> zipWithM (\a b -> (a <: b)) args1' args2'
      (Def q1 args1, Def q2 args2) | q1 == q2 && length args1 == length args2 -> do
        args1' <- map unArg <$> mapM (lift . lift . reduce) args1
        args2' <- map unArg <$> mapM (lift . lift . reduce) args2
        unionConstraints <$> zipWithM (\a b -> (a <: b)) args1' args2'
      (Con con1 args1, Con con2 args2) -> do
        let c1 = conName con1
            c2 = conName con2
        args1' <- map unArg <$> flip notForced args1 <$> getForcedArgs c1
        args2' <- map unArg <$> (mapM (lift . lift . reduce) =<< flip notForced args2 <$> getForcedArgs c2)
        if length args1' == length args2'
            then addConstraint c1 c2 <$> unionConstraints <$> zipWithM (\a b -> (a <: b)) args1' args2'
            else return Nothing
      _ -> return Nothing
-}
data TagEq
    = Same Int
    | IsTag Tag
  deriving Eq

data Tags = Tags
    { eqGroups    :: IntMap (Set QName)
    , constrGroup :: Map QName TagEq
    }

initialTags :: Map QName Tag -> [QName] -> Tags
initialTags setTags newNames = Tags
    { eqGroups    = IntMap.fromList $ zip [0..] (map Set.singleton newNames)
    , constrGroup = Map.map IsTag setTags `Map.union` Map.fromList (zip newNames (map Same [0..]))
    }

unify :: QName -> QName -> Tags -> Compile TCM (Maybe Tags)
unify c1 c2 ts = do
    let g1 = constrGroup ts !!!! c1
        g2 = constrGroup ts !!!! c2
    case (g1, g2) of
        (Same n1, Same n2)   | n1 == n2 -> return $ Just ts
        (IsTag t1, IsTag t2) | t1 == t2 -> return $ Just ts
        (Same n1, Same n2)   -> mergeGroups n1 n2 ts
        (Same n1, IsTag t2)  -> setTag n1 t2 ts
        (IsTag t1 , Same n2) -> setTag n2 t1 ts
        _                    -> return $ Nothing

setTag :: Int -> Tag -> Tags -> Compile TCM (Maybe Tags)
setTag gid tag ts = return $ Just $ ts
    { constrGroup = foldr (\ c -> Map.insert c (IsTag tag))
                          (constrGroup ts)
                          (Set.toList $ fromMaybe __IMPOSSIBLE__ $ IntMap.lookup gid $ eqGroups ts) }

mergeGroups :: Int -> Int -> Tags -> Compile TCM (Maybe Tags)
mergeGroups n1 n2 ts = do
    let g1s = fromMaybe __IMPOSSIBLE__ $ IntMap.lookup n1 $ eqGroups ts
        g2s = fromMaybe __IMPOSSIBLE__ $ IntMap.lookup n2 $ eqGroups ts
        gs  = Set.union g1s g2s
        g1l = Set.toList g1s
        g2l = Set.toList g2s
    ifNotM (andM $ zipWith unifiable g1l g2l)
        (return Nothing) $
        return $ Just $ ts
            { eqGroups    = IntMap.delete n2 $ IntMap.insert n1 gs (eqGroups ts)
            , constrGroup = Map.fromList [ (e2, Same n1) | e2 <- g2l ] `Map.union` constrGroup ts
            }

unifiable :: QName -> QName -> Compile TCM Bool
unifiable c1 c2 = do
    d1 <- getConData c1
    d2 <- getConData c2
    return $ d1 /= d2

(!!!!) :: Ord k => Map k v -> k -> v
m !!!!  k = case Map.lookup k m of
    Nothing -> __IMPOSSIBLE__
    Just x  -> x
