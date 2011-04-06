{-# LANGUAGE CPP, MultiParamTypeClasses, FunctionalDependencies,
             UndecidableInstances, TypeSynonymInstances, FlexibleInstances
  #-}

{-|
    Translating from internal syntax to abstract syntax. Enables nice
    pretty printing of internal syntax.

    TODO

        - numbers on metas
        - fake dependent functions to independent functions
        - meta parameters
        - shadowing
-}
module Agda.Syntax.Translation.InternalToAbstract where

import Prelude hiding (mapM_, mapM)
import Control.Arrow
import Control.Monad.State hiding (mapM_, mapM)
import Control.Monad.Error hiding (mapM_, mapM)

import qualified Data.Set as Set
import Data.Set (Set)
import qualified Data.Map as Map
import Data.Map (Map)
import Data.List hiding (sort)
import Data.Traversable

import Agda.Syntax.Literal
import Agda.Syntax.Position
import Agda.Syntax.Common
import Agda.Syntax.Info as Info
import Agda.Syntax.Fixity
import Agda.Syntax.Abstract as A
import qualified Agda.Syntax.Concrete as C
import Agda.Syntax.Internal as I
import Agda.Syntax.Scope.Base
import Agda.Syntax.Scope.Monad

import Agda.TypeChecking.Monad as M
import Agda.TypeChecking.Reduce
import {-# SOURCE #-} Agda.TypeChecking.Records
import Agda.TypeChecking.DisplayForm
import Agda.TypeChecking.Level
import Agda.TypeChecking.Monad.Builtin
import Agda.TypeChecking.Datatypes
import Agda.TypeChecking.Free
import Agda.TypeChecking.Substitute

import Agda.Utils.Monad
import Agda.Utils.Tuple
import Agda.Utils.Permutation
import Agda.Utils.Size

#include "../../undefined.h"
import Agda.Utils.Impossible

apps :: MonadTCM tcm => (Expr, [Arg Expr]) -> tcm Expr
apps (e, []) = return e
apps (e, arg : args) | isHiddenArg arg =
    do  showImp <- showImplicitArguments
        if showImp then apps (App exprInfo e (unnamed <$> arg), args)
                   else apps (e, args)
apps (e, arg:args)          =
    apps (App exprInfo e (unnamed <$> arg), args)

exprInfo :: ExprInfo
exprInfo = ExprRange noRange

reifyApp :: MonadTCM tcm => Expr -> [Arg Term] -> tcm Expr
reifyApp e vs = curry apps e =<< reify vs

class Reify i a | i -> a where
    reify :: MonadTCM tcm => i -> tcm a

instance Reify MetaId Expr where
    reify x@(MetaId n) = liftTCM $ do
      mi  <- getMetaInfo <$> lookupMeta x
      let mi' = Info.MetaInfo (getRange mi)
                              (M.clScope mi)
                              (Just n)
      ifM shouldReifyInteractionPoints
          (do iis <- map (snd /\ fst) . Map.assocs
                      <$> gets stInteractionPoints
              case lookup x iis of
                Just ii@(InteractionId n)
                        -> return $ A.QuestionMark $ mi' {metaNumber = Just n}
                Nothing -> return $ A.Underscore mi'
          ) (return $ A.Underscore mi')

instance Reify DisplayTerm Expr where
  reify d = case d of
    DTerm v -> reify v
    DDot  v -> reify v
    DCon c vs -> curry apps (A.Con (AmbQ [c])) =<< reify vs
    DDef f vs -> curry apps (A.Def f) =<< reify vs
    DWithApp us vs -> do
      us <- reify us
      let wapp [e] = e
          wapp (e : es) = A.WithApp exprInfo e es
          wapp [] = __IMPOSSIBLE__
      reifyApp (wapp us) vs

reifyDisplayForm :: MonadTCM tcm => QName -> Args -> tcm A.Expr -> tcm A.Expr
reifyDisplayForm x vs fallback = do
  enabled <- displayFormsEnabled
  if enabled
    then do
      md <- liftTCM $ displayForm x vs
      case md of
        Nothing -> fallback
        Just d  -> reify d
    else fallback

reifyDisplayFormP :: A.LHS -> TCM A.LHS
reifyDisplayFormP lhs@(A.LHS i x ps wps) =
  ifM (not <$> displayFormsEnabled) (return lhs) $ do
    let vs = [ Arg h Relevant $ I.Var n [] | (n, h) <- zip [0..] $ map argHiding ps]
    md <- liftTCM $ displayForm x vs
    reportSLn "syntax.reify.display" 20 $
      "display form of " ++ show x ++ " " ++ show ps ++ " " ++ show wps ++ ":\n  " ++ show md
    case md of
      Just d  | okDisplayForm d ->
        reifyDisplayFormP =<< displayLHS (map (namedThing . unArg) ps) wps d
      _ -> return lhs
  where
    okDisplayForm (DWithApp (d : ds) []) =
      okDisplayForm d && all okDisplayTerm ds
    okDisplayForm (DTerm (I.Def f vs)) = all okArg vs
    okDisplayForm (DDef f vs) = all okDArg vs
    okDisplayForm DDot{} = False
    okDisplayForm DCon{} = False
    okDisplayForm DTerm{} = True -- False?
    okDisplayForm DWithApp{} = True -- False?

    okDisplayTerm (DTerm v) = okTerm v
    okDisplayTerm DDot{} = True
    okDisplayTerm DCon{} = True
    okDisplayTerm DDef{} = False
    okDisplayTerm _ = False

    okDArg = okDisplayTerm . unArg
    okArg = okTerm . unArg

    okTerm (I.Var _ []) = True
    okTerm (I.Con c vs) = all okArg vs
    okTerm (I.Def x []) = show x == "_" -- Handling wildcards in display forms
    okTerm _            = True -- False

    flattenWith (DWithApp (d : ds) []) = case flattenWith d of
      (f, vs, ds') -> (f, vs, ds' ++ ds)
    flattenWith (DDef f vs) = (f, vs, [])
    flattenWith (DTerm (I.Def f vs)) = (f, map (fmap DTerm) vs, [])
    flattenWith _ = __IMPOSSIBLE__

    displayLHS ps wps d = case flattenWith d of
      (f, vs, ds) -> do
        ds <- mapM termToPat ds
        vs <- mapM argToPat vs
        return $ LHS i f vs (ds ++ wps)
      where
        info = PatRange noRange
        argToPat arg = fmap unnamed <$> traverse termToPat arg

        len = genericLength ps

        termToPat :: DisplayTerm -> TCM A.Pattern
        termToPat (DTerm (I.Var n [])) = return $ ps !! fromIntegral n
        termToPat (DCon c vs) = A.ConP info (AmbQ [c]) <$> mapM argToPat vs
        termToPat (DDot v) = A.DotP info <$> termToExpr v
        termToPat (DDef _ []) = return $ A.WildP info
        termToPat (DTerm (I.Con c vs)) = A.ConP info (AmbQ [c]) <$> mapM (argToPat . fmap DTerm) vs
        termToPat (DTerm (I.Def _ [])) = return $ A.WildP info
        termToPat v = A.DotP info <$> reify v -- __IMPOSSIBLE__

        argsToExpr = mapM (traverse termToExpr)

        -- TODO: restructure this to avoid having to repeat the code for reify
        termToExpr :: Term -> TCM A.Expr
        termToExpr (I.Var n [])
          | n < len = return $ patToTerm $ ps !! fromIntegral n
        termToExpr (I.Con c vs) =
          curry apps (A.Con (AmbQ [c])) =<< argsToExpr vs
        termToExpr (I.Def f vs) = 
          curry apps (A.Def f) =<< argsToExpr vs
        termToExpr (I.Var n vs) =
          apps =<< (,) <$> reify (I.Var (n - len) []) <*> argsToExpr vs
        termToExpr _ = return $ A.Underscore minfo
          
        minfo = MetaInfo noRange emptyScopeInfo Nothing
        einfo = ExprRange noRange
        app = foldl (App einfo)

        patToTerm :: A.Pattern -> A.Expr
        patToTerm (A.VarP x)      = A.Var x
        patToTerm (A.ConP _ c ps) =
          A.Con c `app` map (fmap (fmap patToTerm)) ps
        patToTerm (A.DefP _ f ps) =
          A.Def f `app` map (fmap (fmap patToTerm)) ps
        patToTerm (A.WildP _)     = A.Underscore minfo
        patToTerm (A.AsP _ _ p)   = patToTerm p
        patToTerm (A.DotP _ e)    = e
        patToTerm (A.AbsurdP _)   = A.Underscore minfo  -- TODO: could this happen?
        patToTerm (A.LitP l)      = A.Lit l
        patToTerm (A.ImplicitP _) = A.Underscore minfo

-- Level literals should be expanded.

instance Reify Literal Expr where
  reify (LitLevel r n) = do
    levelZero <- primLevelZero
    levelSuc  <- levelSucFunction
    reify $ fold levelSuc levelZero n
    where
    fold s z n | n < 0     = __IMPOSSIBLE__
               | otherwise = foldr (.) id (genericReplicate n s) z
  reify l@(LitInt    {}) = return (A.Lit l)
  reify l@(LitFloat  {}) = return (A.Lit l)
  reify l@(LitString {}) = return (A.Lit l)
  reify l@(LitChar   {}) = return (A.Lit l)
  reify l@(LitQName   {}) = return (A.Lit l)

instance Reify Term Expr where
  reify v = do
    v <- instantiate v
    case v of
      I.Var n vs   -> do
          x  <- liftTCM $ nameOfBV n `catchError` \_ -> freshName_ ("@" ++ show n)
          reifyApp (A.Var x) vs
      I.Def x vs   -> reifyDisplayForm x vs $ do
          n <- getDefFreeVars x
          reifyApp (A.Def x) $ genericDrop n vs
      I.Con x vs   -> do
        isR <- isGeneratedRecordConstructor x
        case isR of
          True -> do
            showImp <- showImplicitArguments
            let keep (a, v) = showImp || argHiding a == NotHidden
            r  <- getConstructorData x
            xs <- getRecordFieldNames r
            vs <- reify $ map unArg vs
            return $ A.Rec exprInfo $ map (unArg *** id) $ filter keep $ zip xs vs
          False -> reifyDisplayForm x vs $ do
            -- let hide a = a { argHiding = Hidden }
            Constructor{conPars = np} <- theDef <$> getConstInfo x
            scope <- getScope
            let whocares = A.Underscore (Info.MetaInfo noRange scope Nothing)
                us = replicate (fromIntegral np) $ Arg Hidden Relevant whocares
            n  <- getDefFreeVars x
            es <- reify vs
            apps (A.Con (AmbQ [x]), genericDrop n $ us ++ es)
      I.Lam h b    -> do
        (x,e) <- reify b
        return $ A.Lam exprInfo (DomainFree h x) e
      I.Lit l        -> reify l
      I.Pi a b       -> do
        Arg h r a <- reify a
        (x,b)     <- reify b
        return $ A.Pi exprInfo [TypedBindings noRange $ Arg h r (TBind noRange [x] a)] b
      I.Fun a b    -> uncurry (A.Fun $ exprInfo)
                      <$> reify (a,b)
      I.Sort s     -> reify s
      I.MetaV x vs -> apps =<< reify (x,vs)
      I.DontCare   -> return A.DontCare

data NamedClause = NamedClause QName I.Clause
-- Named clause does not need 'Recursion' flag since I.Clause has it
-- data NamedClause = NamedClause QName Recursion I.Clause

instance Reify ClauseBody RHS where
  reify NoBody     = return AbsurdRHS
  reify (Body v)   = RHS <$> reify v
  reify (NoBind b) = reify b
  reify (Bind b)   = reify $ absBody b  -- the variables should already be bound

stripImplicits :: MonadTCM tcm => [NamedArg A.Pattern] -> [A.Pattern] ->
                  tcm ([NamedArg A.Pattern], [A.Pattern])
stripImplicits ps wps =
  ifM showImplicitArguments (return (ps, wps)) $ do
  let vars = dotVars (ps, wps)
  reportSLn "syntax.reify.implicit" 30 $ unlines
    [ "stripping implicits"
    , "  ps   = " ++ show ps
    , "  wps  = " ++ show wps
    , "  vars = " ++ show vars
    ]
  let allps       = ps ++ map (defaultArg . unnamed) wps
      sps         = foldl (.) (strip vars) (map rearrangeBinding $ Set.toList vars) $ allps
      (ps', wps') = splitAt (length sps - length wps) sps
  reportSLn "syntax.reify.implicit" 30 $ unlines
    [ "  ps'  = " ++ show ps'
    , "  wps' = " ++ show (map (namedThing . unArg) wps')
    ]
  return (ps', map (namedThing . unArg) wps')
  where
    argsVars = Set.unions . map argVars
    argVars = patVars . namedThing . unArg
    patVars p = case p of
      A.VarP x      -> Set.singleton x
      A.ConP _ _ ps -> argsVars ps
      A.DefP _ _ ps -> Set.empty
      A.DotP _ e    -> Set.empty
      A.WildP _     -> Set.empty
      A.AbsurdP _   -> Set.empty
      A.LitP _      -> Set.empty
      A.ImplicitP _ -> Set.empty
      A.AsP _ _ p   -> patVars p

    -- Pick the "best" place to bind the variable. Best in this case
    -- is the left-most explicit binding site. But, of course we can't
    -- do this since binding site might be forced by a parent clause.
    -- Why? Because the binding site we pick might not exist in the
    -- generated with function if it corresponds to a dot pattern.
    rearrangeBinding x ps = ps

    strip dvs ps = stripArgs ps
      where
        stripArgs [] = []
        stripArgs (a : as) = case argHiding a of
          Hidden | canStrip a as -> stripArgs as
          _                      -> stripArg a : stripArgs as

        canStrip a as = and
          [ varOrDot p
          , noInterestingBindings p
          , all (flip canStrip []) $ takeWhile ((Hidden ==) . argHiding) as
          ]
          where p = namedThing $ unArg a

        stripArg a = fmap (fmap stripPat) a

        stripPat p = case p of
          A.VarP _      -> p
          A.ConP i c ps -> A.ConP i c $ stripArgs ps
          A.DefP _ _ _  -> p
          A.DotP _ e    -> p
          A.WildP _     -> p
          A.AbsurdP _   -> p
          A.LitP _      -> p
          A.ImplicitP _ -> p
          A.AsP i x p   -> A.AsP i x $ stripPat p

        noInterestingBindings p =
          Set.null $ dvs `Set.intersection` patVars p

        varOrDot A.VarP{}      = True
        varOrDot A.WildP{}     = True
        varOrDot A.DotP{}      = True
        varOrDot A.ImplicitP{} = True
        varOrDot _             = False


class DotVars a where
  dotVars :: a -> Set Name

instance DotVars a => DotVars (Arg a) where
  dotVars a = if isHiddenArg a then Set.empty else dotVars (unArg a)

instance DotVars a => DotVars (Named s a) where
  dotVars = dotVars . namedThing

instance DotVars a => DotVars [a] where
  dotVars = Set.unions . map dotVars

instance (DotVars a, DotVars b) => DotVars (a, b) where
  dotVars (x, y) = Set.union (dotVars x) (dotVars y)

instance DotVars A.Pattern where
  dotVars p = case p of
    A.VarP _      -> Set.empty
    A.ConP _ _ ps -> dotVars ps
    A.DefP _ _ ps -> dotVars ps
    A.DotP _ e    -> dotVars e
    A.WildP _     -> Set.empty
    A.AbsurdP _   -> Set.empty
    A.LitP _      -> Set.empty
    A.ImplicitP _ -> Set.empty
    A.AsP _ _ p   -> dotVars p

instance DotVars A.Expr where
  dotVars e = case e of
    A.ScopedExpr _ e -> dotVars e
    A.Var x          -> Set.singleton x
    A.Def _          -> Set.empty
    A.Con _          -> Set.empty
    A.Lit _          -> Set.empty
    A.QuestionMark _ -> Set.empty
    A.Underscore _   -> Set.empty
    A.App _ e1 e2    -> dotVars (e1, e2)
    A.WithApp _ e es -> dotVars (e, es)
    A.Lam _ _ e      -> dotVars e
    A.AbsurdLam _ _  -> Set.empty
    A.Pi _ tel e     -> dotVars (tel, e)
    A.Fun _ a b      -> dotVars (a, b)
    A.Set _ _        -> Set.empty
    A.Prop _         -> Set.empty
    A.Let _ _ _      -> __IMPOSSIBLE__
    A.Rec _ es       -> dotVars $ map snd es
    A.ETel _         -> __IMPOSSIBLE__
    A.QuoteGoal {}   -> __IMPOSSIBLE__
    A.Quote {}       -> __IMPOSSIBLE__
    A.DontCare       -> __IMPOSSIBLE__  -- Set.empty

instance DotVars TypedBindings where
  dotVars (TypedBindings _ bs) = dotVars bs

instance DotVars TypedBinding where
  dotVars (TBind _ _ e) = dotVars e
  dotVars (TNoBind e)   = dotVars e

reifyPatterns :: MonadTCM tcm =>
  I.Telescope -> Permutation -> [Arg I.Pattern] -> tcm [NamedArg A.Pattern]
reifyPatterns tel perm ps = evalStateT (reifyArgs ps) 0
  where
    reifyArgs as = map (fmap unnamed) <$> mapM reifyArg as
    reifyArg a   = traverse reifyPat a

    tick = do i <- get; put (i + 1); return i

    translate = (vars !!)
      where
        vars = permute (invertP perm) [0..]

    reifyPat p = case p of
      I.VarP s    -> do
        i <- tick
        let j = translate i
        lift $ A.VarP <$> nameOfBV (size tel - 1 - j)
      I.DotP v -> do
        t <- lift $ reify v
        let vars = Set.map show (dotVars t)
        tick
        if Set.member "()" vars
          then return $ A.DotP i $ A.Underscore mi
          else lift $ A.DotP i <$> reify v
      I.LitP (LitLevel {}) -> __IMPOSSIBLE__
      I.LitP l             -> return (A.LitP l)
      I.ConP c _ ps -> A.ConP i (AmbQ [c]) <$> reifyArgs ps
      where
        i = PatRange noRange
        mi = MetaInfo noRange emptyScopeInfo Nothing

instance Reify NamedClause A.Clause where
  reify (NamedClause f (I.Clause _ tel perm ps body)) = addCtxTel tel $ do
    ps  <- reifyPatterns tel perm ps
    lhs <- liftTCM $ reifyDisplayFormP $ LHS info f ps []
    nfv <- getDefFreeVars f
    lhs <- stripImps $ dropParams nfv lhs
    rhs <- reify body
    return $ A.Clause lhs rhs []
    where
      info = LHSRange noRange
      dropParams n (LHS i f ps wps) = LHS i f (genericDrop n ps) wps
      stripImps (LHS i f ps wps) = do
        (ps, wps) <- stripImplicits ps wps
        return $ LHS i f ps wps

instance Reify Type Expr where
    reify (I.El _ t) = reify t

instance Reify Sort Expr where
    reify s =
        do  s <- instantiateFull s
            case s of
                I.Type (I.Lit (LitLevel _ n)) -> return $ A.Set exprInfo n
                I.Type a -> do
                  a <- reify a
                  return $ A.App exprInfo (A.Set exprInfo 0)
                                          (defaultArg (unnamed a))
                I.Prop       -> return $ A.Prop exprInfo
                I.MetaS x as -> apps =<< reify (x, as)
                I.Suc s      ->
                    do  suc <- freshName_ "suc" -- TODO: hack
                        e   <- reify s
                        return $ A.App exprInfo (A.Var suc) (defaultArg $ unnamed e)
                I.Inf       -> A.Var <$> freshName_ "Setω"
                I.DLub s1 s2 -> do
                  lub <- freshName_ "dLub" -- TODO: hack
                  (e1,e2) <- reify (s1, I.Lam NotHidden $ fmap Sort s2)
                  let app x y = A.App exprInfo x (defaultArg $ unnamed y)
                  return $ A.Var lub `app` e1 `app` e2
                I.Lub s1 s2 ->
                    do  lub <- freshName_ "\\/" -- TODO: hack
                        (e1,e2) <- reify (s1,s2)
                        let app x y = A.App exprInfo x (defaultArg $ unnamed y)
                        return $ A.Var lub `app` e1 `app` e2

instance Reify i a => Reify (Abs i) (Name, a) where
    reify (Abs s v) =
        do  x <- freshName_ s
            e <- addCtx x (defaultArg $ sort I.Prop) -- type doesn't matter
                 $ reify v
            return (x,e)

instance Reify I.Telescope A.Telescope where
  reify EmptyTel = return []
  reify (ExtendTel arg tel) = do
    Arg h rel e <- reify arg
    (x,bs)  <- reify $ betterName tel
    let r = getRange e
    return $ TypedBindings r (Arg h rel (TBind r [x] e)) : bs
    where
      betterName (Abs "_" x) = Abs "z" x
      betterName (Abs s   x) = Abs s   x

instance Reify i a => Reify (Arg i) (Arg a) where
    reify = traverse reify

instance Reify i a => Reify [i] [a] where
    reify = traverse reify

instance (Reify i1 a1, Reify i2 a2) => Reify (i1,i2) (a1,a2) where
    reify (x,y) = (,) <$> reify x <*> reify y

instance (Reify t t', Reify a a')
         => Reify (Judgement t a) (Judgement t' a') where
    reify (HasType i t) = HasType <$> reify i <*> reify t
    reify (IsSort i) = IsSort <$> reify i
