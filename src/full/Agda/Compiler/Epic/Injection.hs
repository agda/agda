{-# LANGUAGE CPP, TypeOperators, PatternGuards #-}
module Agda.Compiler.Epic.Injection where

import Control.Monad.State

import Data.Function
import Data.Ix
import Data.List
import Data.Map(Map)
import qualified Data.Map as M
import Data.Maybe
import Data.Set(Set)
import qualified Data.Set as S

import Agda.Syntax.Common
import Agda.Syntax.Internal as I
import Agda.Syntax.Literal
import Agda.TypeChecking.CompiledClause
import Agda.TypeChecking.Monad hiding ((!!!))
import Agda.TypeChecking.Monad.Builtin
import Agda.TypeChecking.Pretty
import Agda.TypeChecking.Reduce
import Agda.TypeChecking.Substitute
import Agda.TypeChecking.Telescope
import Agda.Utils.Monad
import Agda.Utils.Size
import qualified Agda.Utils.HashMap as HM

import Agda.Compiler.Epic.CompileState
import qualified Agda.Compiler.Epic.FromAgda as FA
import Agda.Compiler.Epic.Interface as Interface

#include "../../undefined.h"
import Agda.Utils.Impossible

-- | Find potentially injective functions, solve constraints to fix some constructor
--   tags and make functions whose constraints are fulfilled injections
findInjection :: [(QName, Definition)] -> Compile TCM [(QName, Definition)]
findInjection defs = do
    funs <- forM defs $ \(name, def) -> case theDef def of
        f@(Function{}) -> isInjective name (funClauses f)
        _              -> return Nothing
    newNames <- M.keys <$> gets (Interface.conArity . curModule)
    injFuns <- solve newNames (catMaybes funs)
    defs' <- forM defs $ \(q, def) -> case q `isIn` injFuns of
        Nothing -> return (q, def)
        Just inj@(InjectiveFun nvar arity) -> case theDef def of
            f@(Function{})   -> do
                modifyEI $ \s -> s { injectiveFuns = M.insert q inj (injectiveFuns s) }
                let ns = replicate arity (defaultArg "")
                return $ (,) q $ def { theDef = f { funCompiled = Done ns $
                                                      var $ arity - nvar - 1 } }
            _                -> __IMPOSSIBLE__

    lift $ reportSLn "epic.injection" 10 $ "injfuns: " ++ show injFuns
    return defs'
  where
    q `isIn` funs = case filter (\(nam, _) -> q == nam) funs of
        []   -> Nothing
        (_,x):_  -> Just x

replaceFunCC :: QName -> CompiledClauses -> Compile TCM ()
replaceFunCC name cc = do
    lift $ modify $ \s ->
        s { stSignature = (stSignature s) { sigDefinitions = HM.adjust replaceDef name (sigDefinitions (stSignature s)) }
          , stImports   = (stImports   s) { sigDefinitions = HM.adjust replaceDef name (sigDefinitions (stImports   s)) }
          }
  where
    replaceDef :: Definition -> Definition
    replaceDef def = case theDef def of
        f@(Function{}) -> def {theDef = f { funCompiled = cc } }
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
    let total = genericLength . clausePats $ cl
    (listToMaybe . catMaybes <$>) . forM [0 .. total - 1] $ \i -> do
        cli <- forM cls $ \ cl -> isInjectiveHere nam i  cl
        let cli' = catMaybes cli
        return $ if length cli == length cli'
             then Just ((nam, InjectiveFun i total), concat cli')
             else Nothing

remAbs :: ClauseBody -> Term
remAbs b = case b of
    Body t     -> t
    Bind ab    -> remAbs $ absBody ab
    NoBody     -> __IMPOSSIBLE__

isNoBody :: ClauseBody -> Bool
isNoBody b = case b of
    Body t     -> False
    Bind ab    -> isNoBody $ absBody ab
    NoBody     -> True

patternToTerm :: Nat -> Pattern -> Term
patternToTerm n p = case p of
    VarP v          -> var n
    DotP t          -> t
    ConP c typ args -> Con c $ zipWith (\ arg t -> arg {unArg = t}) args
                             $ snd
                             $ foldr (\ arg (n, ts) -> (n + nrBinds arg, patternToTerm n arg : ts))
                                     (n , [])
                             $ map unArg args
    LitP l          -> Lit l

nrBinds :: Num i => Pattern -> i
nrBinds p = case p of
    VarP v          -> 1
    DotP t          -> 0
    ConP c typ args -> sum $ map (nrBinds . unArg) args
    LitP l          -> 0

substForDot :: [I.Arg Pattern] -> Substitution
substForDot = makeSubst 0 0 . reverse . calcDots
  where
    makeSubst i accum [] = raiseS (i + accum)
    makeSubst i accum (True  : ps) = makeSubst i (accum +1) ps
    makeSubst i accum (False : ps) = var (i + accum) :# makeSubst (i+1) accum ps

    calcDots = concatMap calcDots' . map unArg
    calcDots' p = case p of
        VarP v          -> [False]
        DotP t          -> [True]
        ConP c typ args -> calcDots args
        LitP l          -> [False]

isInjectiveHere :: QName  -- ^ Name of the function being tested
                -> Int    -- ^ The current argument
                -> Clause
                -> Compile TCM InjConstraints
isInjectiveHere nam idx Clause {clauseBody = body} | isNoBody body = return emptyC
isInjectiveHere nam idx clause = do
    let t    = patternToTerm idxR $ unArg $ clausePats clause !! idx
        t'   = applySubst (substForDot $ clausePats clause) t
        idxR = sum . map (nrBinds . unArg) . genericDrop (idx + 1) $ clausePats clause
        body = remAbs $ clauseBody clause
    body' <- lift $ reduce body
    injFs <- gets (injectiveFuns . importedModules)
    res <- (t' <: body') (M.insert nam (InjectiveFun idx
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

litToCon :: Literal -> TCM Term
litToCon l = case l of
    LitInt   r n | n > 0     -> do
        inner <- litToCon (LitInt r (n - 1))
        suc   <- primSuc
        return $ suc `apply` [defaultArg inner]
                 | otherwise -> primZero
--    LitLevel _ n -> -- Does not really matter
    lit          -> return $ Lit lit

litCon :: Literal -> Bool
litCon (LitInt _ _) = True
litCon _          = False

insertAt :: (Nat,Term) -> Term -> Term
insertAt (index, ins) =
  applySubst ([var i | i <- [0 .. index - 1]] ++# ins :# raiseS (index + 1))

solve :: [QName] -> [((QName, InjectiveFun), [(QName,QName)])] -> Compile TCM [(QName, InjectiveFun)]
solve newNames xs = do
    -- Only primitive lists should be in the current module at this point,
    -- but we still want them
    conGraph <- M.union <$> gets (constrTags . curModule) <*> gets (constrTags . importedModules)
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
        let (hasTags, eqs) = M.partition isTag (constrGroup tags)
            isTag (IsTag _) = True
            isTag _         = False
        forM (M.toList hasTags) $ \ (c, tagged) -> case tagged of
            IsTag tag -> putCon c tag
            _         -> __IMPOSSIBLE__
        case M.toList eqs of
            (c, Same n) : _ -> do
                let grp = eqGroups tags !!! n
                tag <- assignConstrTag' c (S.toList grp)
                updateTags . fromMaybe __IMPOSSIBLE__ =<< setTag n tag tags { constrGroup = eqs }
            _              -> return ()
    putCon :: QName -> Tag -> Compile TCM ()
    putCon con tag = do
        m <- gets (constrTags . importedModules)
        case M.lookup con m of
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
--   Precondition: t1 is normalised, t2 is in WHNF
-- When reducing t2, it may become a literal, which makes this not work in some cases...
(<:) :: Term -> Term -> (QName :-> InjectiveFun) -> Compile TCM InjConstraints
(Lit l        <:  t1)          injs | litCon l = do
    l' <- lift $ litToCon l
    (l' <: t1) injs
(t1 <: Lit l)                  injs | litCon l = do
    l' <- lift $ litToCon l
    (t1 <: l') injs
(t1           <: Def n2 args2) injs | Just (InjectiveFun argn arit) <- M.lookup n2 injs =
    if genericLength args2 /= arit
        then return Nothing
        else do
            arg <- lift $ reduce $ unArg $ args2 !! argn
            (t1 <: arg) injs
-- (Var n1 []    <: Var n2 [])    nam idx = return $ if n1 == n2 then emptyC else Nothing
(Var n1 args1 <: Var n2 args2) injs | n1 == n2 && length args1 == length args2 = do
    args1' <- map unArg <$> mapM (lift . reduce) args1
    args2' <- map unArg <$> mapM (lift . reduce) args2
    unionConstraints <$> zipWithM (\a b -> (a <: b) injs) args1' args2'
(Def q1 args1 <: Def q2 args2) injs | q1 == q2 && length args1 == length args2 = do
    args1' <- map unArg <$> mapM (lift . reduce) args1
    args2' <- map unArg <$> mapM (lift . reduce) args2
    unionConstraints <$> zipWithM (\a b -> (a <: b) injs) args1' args2'
(Con c1 args1 <: Con c2 args2) injs = do
    args1' <- map unArg <$> flip notForced args1 <$> getForcedArgs c1
    args2' <- map unArg <$> (mapM (lift . reduce) =<< flip notForced args2 <$> getForcedArgs c2)
    if length args1' == length args2'
        then addConstraint c1 c2 <$> unionConstraints <$> zipWithM (\a b -> (a <: b) injs) args1' args2'
        else return Nothing
(_            <: _) _ = return Nothing

data TagEq
    = Same Int
    | IsTag Tag
  deriving Eq

data Tags = Tags
    { eqGroups    :: Int :-> Set QName
    , constrGroup :: QName :-> TagEq
    }

initialTags :: Map QName Tag -> [QName] -> Tags
initialTags setTags newNames = Tags
    { eqGroups    = M.fromList $ zip [0..] (map S.singleton newNames)
    , constrGroup = M.map IsTag setTags `M.union` M.fromList (zip newNames (map Same [0..]))
    }

unify :: QName -> QName -> Tags -> Compile TCM (Maybe Tags)
unify c1 c2 ts = do
    let g1 = constrGroup ts !!! c1
        g2 = constrGroup ts !!! c2
    case (g1, g2) of
        (Same n1, Same n2)   | n1 == n2 -> return $ Just ts
        (IsTag t1, IsTag t2) | t1 == t2 -> return $ Just ts
        (Same n1, Same n2)   -> mergeGroups n1 n2 ts
        (Same n1, IsTag t2)  -> setTag n1 t2 ts
        (IsTag t1 , Same n2) -> setTag n2 t1 ts
        _                    -> return $ Nothing

setTag :: Int -> Tag -> Tags -> Compile TCM (Maybe Tags)
setTag gid tag ts = return $ Just $ ts
    { constrGroup = foldr (\c -> M.insert c (IsTag tag)) (constrGroup ts) (S.toList $ eqGroups ts !!! gid)}

mergeGroups :: Int -> Int -> Tags -> Compile TCM (Maybe Tags)
mergeGroups n1 n2 ts = do
    let g1s = eqGroups ts !!! n1
        g2s = eqGroups ts !!! n2
        gs  = S.union g1s g2s
    ifM (not <$> andM [unifiable e1 e2 | e1 <- S.toList g1s, e2 <- S.toList g2s])
        (return Nothing) $
        return $ Just $ ts
            { eqGroups    = M.delete n2 $ M.insert n1 gs (eqGroups ts)
            , constrGroup = M.fromList [(e2, Same n1) | e2 <- S.toList g2s] `M.union` constrGroup ts
            }

unifiable :: QName -> QName -> Compile TCM Bool
unifiable c1 c2 = do
    d1 <- getConData c1
    d2 <- getConData c2
    return $ d1 /= d2

(!!!) :: Ord k => k :-> v -> k -> v
m !!!  k = case M.lookup k m of
    Nothing -> __IMPOSSIBLE__
    Just x  -> x
