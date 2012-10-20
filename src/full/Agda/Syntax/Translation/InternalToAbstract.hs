{-# LANGUAGE CPP, MultiParamTypeClasses, FunctionalDependencies,
             UndecidableInstances, TypeSynonymInstances, FlexibleInstances,
             ScopedTypeVariables
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
module Agda.Syntax.Translation.InternalToAbstract
  ( Reify(..)
  , ReifyWhen(..)
  , NamedClause(..)
  , reifyPatterns
  ) where

import Prelude hiding (mapM_, mapM)
import Control.Applicative
import Control.Arrow
import Control.Monad.State hiding (mapM_, mapM)
import Control.Monad.Error hiding (mapM_, mapM)

import qualified Data.Set as Set
import Data.Set (Set)
import qualified Data.Map as Map
import Data.Map (Map)
import Data.List hiding (sort)
import Data.Traversable as Trav

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

import Agda.TypeChecking.Monad as M hiding (MetaInfo)
import Agda.TypeChecking.Reduce
import {-# SOURCE #-} Agda.TypeChecking.Records
import Agda.TypeChecking.DisplayForm
import Agda.TypeChecking.Level
import Agda.TypeChecking.Monad.Builtin
import Agda.TypeChecking.Datatypes
import Agda.TypeChecking.Free
import Agda.TypeChecking.Substitute
import Agda.TypeChecking.Telescope
import Agda.TypeChecking.DropArgs

import Agda.Utils.Monad
import Agda.Utils.Tuple
import Agda.Utils.Permutation
import Agda.Utils.Size

#include "../../undefined.h"
import Agda.Utils.Impossible

-- Composition reified applications ---------------------------------------

napps :: Expr -> [NamedArg Expr] -> TCM Expr
napps e args = do
  dontShowImp <- not <$> showImplicitArguments
  let apply1 e arg | isHiddenArg arg && dontShowImp = e
                   | otherwise = App exprInfo e arg
  return $ foldl' apply1 e args

apps :: Expr -> [Arg Expr] -> TCM Expr
apps e args = napps e $ map (fmap unnamed) args

reifyApp :: Expr -> [Arg Term] -> TCM Expr
reifyApp e vs = apps e =<< reify vs

-- Omitting information ---------------------------------------------------

exprInfo :: ExprInfo
exprInfo = ExprRange noRange

underscore :: Expr
underscore = A.Underscore $ Info.emptyMetaInfo

-- Conditional reification to omitt terms that are not shown --------------

-- | @ReifyWhen@ is a auxiliary type class to reify 'Arg'.
--
--   @reifyWhen False@ should produce an 'underscore'.
--   This function serves to reify hidden/irrelevant things.
class Reify i a => ReifyWhen i a where
    reifyWhen :: Bool -> i -> TCM a
    reifyWhen _ = reify

instance Reify i Expr => ReifyWhen i Expr where
  reifyWhen True  i = reify i
  reifyWhen False t = return underscore

instance ReifyWhen i a => ReifyWhen (Arg i) (Arg a) where
  reifyWhen b = traverse (reifyWhen b)

instance ReifyWhen i a => ReifyWhen (Named n i) (Named n a) where
  reifyWhen b = traverse (reifyWhen b)

-- Reification ------------------------------------------------------------

class Reify i a | i -> a where
    reify     ::         i -> TCM a

instance Reify Expr Expr where
    reify = return

instance Reify MetaId Expr where
    reify x@(MetaId n) = liftTCM $ do
      mi  <- mvInfo <$> lookupMeta x
      let mi' = Info.MetaInfo
                 { metaRange          = getRange $ miClosRange mi
                 , metaScope          = M.clScope $ miClosRange mi
                 , metaNumber         = Just n
                 , metaNameSuggestion = miNameSuggestion mi
                 }
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
    DTerm v -> reifyTerm False v
    DDot  v -> reify v
    DCon c vs -> apps (A.Con (AmbQ [c])) =<< reify vs
    DDef f vs -> apps (A.Def f) =<< reify vs
    DWithApp us vs -> do
      us <- reify us
      let wapp [e] = e
          wapp (e : es) = A.WithApp exprInfo e es
          wapp [] = __IMPOSSIBLE__
      reifyApp (wapp us) vs

reifyDisplayForm :: QName -> Args -> TCM A.Expr -> TCM A.Expr
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
reifyDisplayFormP lhs@(A.LHS i A.LHSProj{} wps) =
  typeError $ NotImplemented "reifyDisplayForm for copatterns"
reifyDisplayFormP lhs@(A.LHS i (A.LHSHead x ps) wps) =
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
        return $ LHS i (LHSHead f vs) (ds ++ wps)
      where
        info = PatRange noRange
        argToPat arg = fmap unnamed <$> traverse termToPat arg

        len = genericLength ps

        termToPat :: DisplayTerm -> TCM A.Pattern
        termToPat (DTerm (I.Var n [])) = return $ ps !! n
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
          | n < len = return $ A.patternToExpr $ ps !! n
        termToExpr (I.Con c vs) =
          apps (A.Con (AmbQ [c])) =<< argsToExpr vs
        termToExpr (I.Def f vs) =
          apps (A.Def f) =<< argsToExpr vs
        termToExpr (I.Var n vs) =
          uncurry apps =<< (,) <$> reify (I.var (n - len)) <*> argsToExpr vs
        termToExpr _ = return underscore

instance Reify Literal Expr where
  reify l@(LitInt    {}) = return (A.Lit l)
  reify l@(LitFloat  {}) = return (A.Lit l)
  reify l@(LitString {}) = return (A.Lit l)
  reify l@(LitChar   {}) = return (A.Lit l)
  reify l@(LitQName  {}) = return (A.Lit l)

instance Reify Term Expr where
  reify v = reifyTerm True v

reifyTerm :: Bool -> Term -> TCM Expr
reifyTerm expandAnonDefs v = do
    v <- instantiate v
    case v of
      I.Var n vs   -> do
          x  <- liftTCM $ nameOfBV n `catchError` \_ -> freshName_ ("@" ++ show n)
          reifyApp (A.Var x) vs
      I.Def x vs   -> reifyDisplayForm x vs $ reifyDef expandAnonDefs x vs
      I.Con x vs   -> do
        isR <- isGeneratedRecordConstructor x
        case isR of
          True -> do
            showImp <- showImplicitArguments
            let keep (a, v) = showImp || argHiding a == NotHidden
            r  <- getConstructorData x
            xs <- getRecordFieldNames r
            vs <- map unArg <$> reify vs
            return $ A.Rec exprInfo $ map (unArg *** id) $ filter keep $ zip xs vs
          False -> reifyDisplayForm x vs $ do
            ci <- getConstInfo x
            let Constructor{conPars = np} = theDef ci
            -- if we are the the module that defines constructor x
            -- then we have to drop at least the n module parameters
            n  <- getDefFreeVars x
            -- the number of parameters is greater (if the data decl has
            -- extra parameters) or equal (if not) to n
            when (n > np) __IMPOSSIBLE__
            let h = A.Con (AmbQ [x])
            if null vs then return h else do
            es <- reify vs
            -- Andreas, 2012-04-20: do not reify parameter arguments of constructor
            -- if the first regular constructor argument is hidden
            -- we turn it into a named argument, in order to avoid confusion
            -- with the parameter arguments which can be supplied in abstract syntax
            --
            -- Andreas, 2012-09-17: this does not remove all sources of confusion,
            -- since parameters could have the same name as regular arguments
            -- (see for example the parameter {i} to Data.Star.Star, which is also
            -- the first argument to the cons).
            -- @data Star {i}{I : Set i} ... where cons : {i :  I} ...@
            if (np == 0) then apps h es  -- if np==0 then n==0
            -- WAS: if (np == 0) then apps h $ genericDrop n es
             else do   -- get name of argument from type of constructor
              TelV tel _ <- telView (defType ci) -- need reducing version of telView because target of constructor could be a definition expanding into a function type
              let -- TelV tel _ = telView' (defType ci) -- WRONG, see test/suceed/NameFirstIfHidden
                  doms       = genericDrop np $ telToList tel
              case doms of
                -- Andreas, 2012-09-18
                -- If the first regular constructor argument is hidden,
                -- we keep the parameters to avoid confusion.
                (Dom Hidden _ _ : _) -> do
                  let us = genericReplicate (np - n) $ Arg Hidden Relevant underscore
                  apps h $ us ++ es
                -- otherwise, we drop all parameters
                _ -> apps h es
{- CODE FROM 2012-04-xx
              reportSLn "syntax.reify.con" 30 $ unlines
                [ "calling nameFirstIfHidden"
                , "doms = " ++ show doms
                , "es   = " ++ show es
                , "n    = " ++ show n
                , "np   = " ++ show np
                ]
              napps h $ genericDrop (n - np) $ nameFirstIfHidden doms es
-}
      I.Lam h b    -> do
        (x,e) <- reify b
        return $ A.Lam exprInfo (DomainFree h Relevant x) e
        -- Andreas, 2011-04-07 we do not need relevance information at internal Lambda
      I.Lit l        -> reify l
      I.Level l      -> reify l
      I.Pi a b       -> case b of
        NoAbs _ b -> uncurry (A.Fun $ exprInfo) <$> reify (a,b)
        b         -> do
          Arg h r a <- reify a
          (x, b)    <- reify b
          return $ A.Pi exprInfo [TypedBindings noRange $ Arg h r (TBind noRange [x] a)] b
      I.Sort s     -> reify s
      I.MetaV x vs -> uncurry apps =<< reify (x,vs)
      I.DontCare v -> A.DontCare <$> reifyTerm expandAnonDefs v
      I.Shared p   -> reifyTerm expandAnonDefs $ derefPtr p

    where
      -- Andreas, 2012-10-20  expand a copy in an anonymous module
      -- to improve error messages.
      -- Don't do this if we have just expanded into a display form,
      -- otherwise we loop!
      reifyDef True x@(QName m name) vs | A.isAnonymousModuleName m = do
        r <- reduceDefCopy x vs
        case r of
          YesReduction v -> do
            reportSLn "reify.anon" 20 $ unlines
              [ "reduction on defined ident. in anonymous module"
              , "x = " ++ show x
              , "v = " ++ show v
              ]
            reify v
          NoReduction () -> do
            reportSLn "reify.anon" 20 $ unlines
              [ "no reduction on defined ident. in anonymous module"
              , "x  = " ++ show x
              , "vs = " ++ show vs
              ]
            reifyDef' x vs
      reifyDef _ x vs = reifyDef' x vs

      reifyDef' x@(QName _ name) vs = do
        mdefn <- liftTCM $ (Just <$> getConstInfo x) `catchError` \_ -> return Nothing
        (pad, vs :: [NamedArg Term]) <-
          case mdefn of
            Nothing -> (,) [] <$> do map (fmap unnamed) <$> (flip genericDrop vs <$> getDefFreeVars x)
            Just defn -> do
              let def = theDef defn
              -- This is tricky:
              --  * getDefFreeVars x tells us how many arguments
              --    are part of the local context
              --  * some of those arguments might have been dropped
              --    due to projection likeness
              --  * when showImplicits is on we'd like to see the dropped
              --    projection arguments

              -- We should drop this many arguments from the local context.
              n <- getDefFreeVars x
              -- These are the dropped projection arguments
              (np, pad, dom) <-
                  case def of
                      Function{ funProjection = Just (_, np) } -> do
                        TelV tel _ <- telView (defType defn)
                        scope <- getScope
                        let (as, dom:_) = splitAt (np - 1) $ telToList tel
                            whocares = A.Underscore $ Info.emptyMetaInfo { metaScope = scope }
                        return (np, map (argFromDom . (fmap $ const whocares)) as, dom)
                      _ -> return (0, [], __IMPOSSIBLE__)
              -- Now pad' ++ vs' = drop n (pad ++ vs)
              let pad' = genericDrop n pad
                  vs'  :: [Arg Term]
                  vs'  = genericDrop (max 0 (n - size pad)) vs
              -- Andreas, 2012-04-21: get rid of hidden underscores {_}
              -- Keep non-hidden arguments of the padding
              showImp <- showImplicitArguments
              return (filter (not . isHiddenArg) pad',
                if not (null pad) && showImp && isHiddenArg (last pad)
                   then nameFirstIfHidden [dom] vs'
                   else map (fmap unnamed) vs')
        df <- displayFormsEnabled
        if df && isPrefixOf extendlambdaname (show name)
          then do
           reportSLn "int2abs.reifyterm.def" 10 $ "reifying extended lambda with definition: " ++ show x
           info <- getConstInfo x
           --drop lambda lifted arguments
           Just (h , nh) <- Map.lookup x <$> getExtLambdaTele
           let n = h + nh
           cls <- mapM (reify . (NamedClause x) . (dropArgs n)) $ defClauses info
           -- Karim: Currently Abs2Conc does not require a DefInfo thus we
           -- use __IMPOSSIBLE__.
           napps (A.ExtendedLam exprInfo __IMPOSSIBLE__ x cls) =<< reify vs
          else do
           let apps = foldl' (\e a -> A.App exprInfo e (fmap unnamed a))
           napps (A.Def x `apps` pad) =<< reify vs

-- | @nameFirstIfHidden n (a1->...an->{x:a}->b) ({e} es) = {x = e} es@
nameFirstIfHidden :: [Dom (String, t)] -> [Arg a] -> [NamedArg a]
nameFirstIfHidden _         []                    = []
nameFirstIfHidden []        (_ : _)               = __IMPOSSIBLE__
nameFirstIfHidden (dom : _) (Arg Hidden r e : es) =
  Arg Hidden r (Named (Just $ fst $ unDom dom) e) : map (fmap unnamed) es
nameFirstIfHidden _         es                    = map (fmap unnamed) es

instance Reify i a => Reify (Named n i) (Named n a) where
  reify = traverse reify

-- | Skip reification of implicit and irrelevant args if option is off.
instance (ReifyWhen i a) => Reify (Arg i) (Arg a) where
  reify (Arg h r i) = Arg h r <$> do flip reifyWhen i =<< condition
    where condition = (return (h /= Hidden) `or2M` showImplicitArguments)
              `and2M` (return (r /= Irrelevant) `or2M` showIrrelevantArguments)

instance Reify Elim Expr where
  reify e = case e of
    I.Apply v -> appl "apply" <$> reify v
    I.Proj f  -> appl "proj"  <$> reify (defaultArg $ I.Def f [])
    where
      appl :: String -> Arg Expr -> Expr
      appl s v = A.App exprInfo (A.Lit (LitString noRange s)) $ fmap unnamed v

data NamedClause = NamedClause QName I.Clause
-- Named clause does not need 'Recursion' flag since I.Clause has it
-- data NamedClause = NamedClause QName Recursion I.Clause

instance Reify ClauseBody RHS where
  reify NoBody     = return AbsurdRHS
  reify (Body v)   = RHS <$> reify v
  reify (Bind b)   = reify $ absBody b  -- the variables should already be bound

stripImplicits :: [NamedArg A.Pattern] -> [A.Pattern] ->
                  TCM ([NamedArg A.Pattern], [A.Pattern])
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
      A.PatternSynP _ _ _ -> __IMPOSSIBLE__ -- Set.empty

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
          A.PatternSynP _ _ _ -> __IMPOSSIBLE__ -- p

        noInterestingBindings p =
          Set.null $ dvs `Set.intersection` patVars p

        varOrDot A.VarP{}      = True
        varOrDot A.WildP{}     = True
        varOrDot A.DotP{}      = True
        varOrDot A.ImplicitP{} = True
        varOrDot _             = False

-- | @dotVars ps@ gives all the variables inside of dot patterns of @ps@
--   It is only invoked for patternish things. (Ulf O-tone!)
--   Use it for printing l.h.sides: which of the implicit arguments
--   have to be made explicit.
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


instance DotVars A.Clause where
  dotVars (A.Clause _ rhs []) = dotVars rhs
  dotVars (A.Clause _ rhs (_:_)) = __IMPOSSIBLE__ -- cannot contain where clauses?

instance DotVars A.Pattern where
  dotVars p = case p of
    A.VarP _      -> Set.empty   -- do not add pattern vars
    A.ConP _ _ ps -> dotVars ps
    A.DefP _ _ ps -> dotVars ps
    A.DotP _ e    -> dotVars e
    A.WildP _     -> Set.empty
    A.AbsurdP _   -> Set.empty
    A.LitP _      -> Set.empty
    A.ImplicitP _ -> Set.empty
    A.AsP _ _ p   -> dotVars p
    A.PatternSynP _ _ _ -> __IMPOSSIBLE__ -- Set.empty

-- | Getting all(!) variables of an expression.
--   It should only get free ones, but it does not matter to include
--   the bound ones.
instance DotVars A.Expr where
  dotVars e = case e of
    A.ScopedExpr _ e       -> dotVars e
    A.Var x                -> Set.singleton x -- add any expression variable
    A.Def _                -> Set.empty
    A.Con _                -> Set.empty
    A.Lit _                -> Set.empty
    A.QuestionMark _       -> Set.empty
    A.Underscore _         -> Set.empty
    A.App _ e1 e2          -> dotVars (e1, e2)
    A.WithApp _ e es       -> dotVars (e, es)
    A.Lam _ _ e            -> dotVars e
    A.AbsurdLam _ _        -> Set.empty
    A.ExtendedLam _ _ _ cs -> dotVars cs
    A.Pi _ tel e           -> dotVars (tel, e)
    A.Fun _ a b            -> dotVars (a, b)
    A.Set _ _              -> Set.empty
    A.Prop _               -> Set.empty
    A.Let _ _ _            -> __IMPOSSIBLE__
    A.Rec _ es             -> dotVars $ map snd es
    A.RecUpdate _ e es     -> dotVars (e, map snd es)
    A.ETel _               -> __IMPOSSIBLE__
    A.QuoteGoal {}         -> __IMPOSSIBLE__
    A.Quote {}             -> __IMPOSSIBLE__
    A.QuoteTerm {}         -> __IMPOSSIBLE__
    A.Unquote {}           -> __IMPOSSIBLE__
    A.DontCare v           -> dotVars v
    A.PatternSyn n         -> Set.empty

instance DotVars RHS where
  dotVars (RHS e) = dotVars e
  dotVars AbsurdRHS = Set.empty
  dotVars (WithRHS _ es clauses) = __IMPOSSIBLE__ -- NZ
  dotVars (RewriteRHS _ es rhs _) = __IMPOSSIBLE__ -- NZ

instance DotVars TypedBindings where
  dotVars (TypedBindings _ bs) = dotVars bs

instance DotVars TypedBinding where
  dotVars (TBind _ _ e) = dotVars e
  dotVars (TNoBind e)   = dotVars e

reifyPatterns :: I.Telescope -> Permutation -> [Arg I.Pattern] -> TCM [NamedArg A.Pattern]
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
          then return $ A.DotP i $ underscore
          else return $ A.DotP i t
      I.LitP l             -> return (A.LitP l)
      I.ConP c _ ps -> A.ConP i (AmbQ [c]) <$> reifyArgs ps
      where
        i = PatRange noRange

instance Reify NamedClause A.Clause where
  reify (NamedClause f (I.Clause _ tel perm ps body)) = addCtxTel tel $ do
    ps  <- reifyPatterns tel perm ps
    lhs <- liftTCM $ reifyDisplayFormP $ LHS info (LHSHead f ps) []
    nfv <- getDefFreeVars f
    lhs <- stripImps $ dropParams nfv lhs
    rhs <- reify body
    return $ A.Clause lhs rhs []
    where
      info = LHSRange noRange
      dropParams n (LHS i lhscore wps) =
        LHS i (mapLHSHead (\ f ps -> LHSHead f (genericDrop n ps)) lhscore) wps
      stripImps (LHS i lhscore wps) = do
          (wps', lhscore) <- stripIs lhscore
          return $ LHS i lhscore wps'
        where stripIs (LHSHead f ps) = do
                (ps, wps) <- stripImplicits ps wps
                return (wps, LHSHead f ps)
              stripIs (LHSProj d ps1 l ps2) = do
                Arg h r (Named n (wps, l)) <- Trav.mapM (Trav.mapM stripIs) l
                return (wps, LHSProj d ps1 (Arg h r (Named n l)) ps2)
{-
      dropParams n (LHS i (LHSHead f ps) wps) = LHS i (LHSHead f (genericDrop n ps)) wps
      stripImps (LHS i (LHSHead f ps) wps) = do
        (ps, wps) <- stripImplicits ps wps
        return $ LHS i (LHSHead f ps) wps
-}

instance Reify Type Expr where
    reify (I.El _ t) = reify t

instance Reify Sort Expr where
    reify s =
        do  s <- instantiateFull s
            case s of
                I.Type (I.Max [])                -> return $ A.Set exprInfo 0
                I.Type (I.Max [I.ClosedLevel n]) -> return $ A.Set exprInfo n
                I.Type a -> do
                  a <- reify a
                  return $ A.App exprInfo (A.Set exprInfo 0)
                                          (defaultArg (unnamed a))
                I.Prop       -> return $ A.Prop exprInfo
                I.Inf       -> A.Var <$> freshName_ "Setω"
                I.DLub s1 s2 -> do
                  lub <- freshName_ "dLub" -- TODO: hack
                  (e1,e2) <- reify (s1, I.Lam NotHidden $ fmap Sort s2)
                  let app x y = A.App exprInfo x (defaultArg $ unnamed y)
                  return $ A.Var lub `app` e1 `app` e2

instance Reify Level Expr where
  reify l = reify =<< reallyUnLevelView l

instance (Free i, Reify i a) => Reify (Abs i) (Name, a) where
  reify (NoAbs x v) = (,) <$> freshName_ x <*> reify v
  reify (Abs s v) = do

    -- If the bound variable is free in the body, then the name "_" is
    -- replaced by "z".
    s <- return $ if s == "_" && 0 `freeIn` v then "z" else s

    x <- freshName_ s
    e <- addCtx x dummyDom -- type doesn't matter
         $ reify v
    return (x,e)

instance Reify I.Telescope A.Telescope where
  reify EmptyTel = return []
  reify (ExtendTel arg tel) = do
    Arg h rel e <- reify arg
    (x,bs)  <- reify tel
    let r = getRange e
    return $ TypedBindings r (Arg h rel (TBind r [x] e)) : bs

instance Reify i a => Reify (Dom i) (Arg a) where
    reify (Dom h r i) = Arg h r <$> reify i

instance Reify i a => Reify [i] [a] where
    reify = traverse reify

instance (Reify i1 a1, Reify i2 a2) => Reify (i1,i2) (a1,a2) where
    reify (x,y) = (,) <$> reify x <*> reify y

instance (Reify t t', Reify a a')
         => Reify (Judgement t a) (Judgement t' a') where
    reify (HasType i t) = HasType <$> reify i <*> reify t
    reify (IsSort  i t) = IsSort  <$> reify i <*> reify t
