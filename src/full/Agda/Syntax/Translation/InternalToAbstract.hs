{-# LANGUAGE CPP                    #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE NondecreasingIndentation #-}
{-# LANGUAGE ScopedTypeVariables    #-}
{-# LANGUAGE UndecidableInstances   #-}

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
  , NamedClause(..)
  , reifyPatterns
  ) where

import Prelude hiding (mapM_, mapM, null)
import Control.Applicative hiding (empty)
import Control.Monad.State hiding (mapM_, mapM)
import Control.Monad.Reader hiding (mapM_, mapM)

import Data.Foldable (foldMap)
import Data.List hiding (null, sort)
import qualified Data.Map as Map
import Data.Maybe
import Data.Semigroup (Semigroup, Monoid, (<>), mempty, mappend)
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Traversable (traverse, mapM)
import qualified Data.Traversable as Trav

import Agda.Syntax.Literal
import Agda.Syntax.Position
import Agda.Syntax.Common
import Agda.Syntax.Fixity
import Agda.Syntax.Concrete (FieldAssignment'(..), exprFieldA)
import Agda.Syntax.Info as Info
import Agda.Syntax.Abstract as A
import Agda.Syntax.Abstract.Pretty
import Agda.Syntax.Internal as I
import Agda.Syntax.Internal.Pattern as I
import Agda.Syntax.Scope.Base (isNameInScope, inverseScopeLookupName)

import Agda.TypeChecking.Monad
import Agda.TypeChecking.Monad.Builtin
import Agda.TypeChecking.Reduce
import {-# SOURCE #-} Agda.TypeChecking.Records
import Agda.TypeChecking.CompiledClause (CompiledClauses(Fail))
import Agda.TypeChecking.DisplayForm
import Agda.TypeChecking.Level
import {-# SOURCE #-} Agda.TypeChecking.Datatypes
import Agda.TypeChecking.Free
import Agda.TypeChecking.Substitute
import Agda.TypeChecking.Telescope
import Agda.TypeChecking.DropArgs

import Agda.Utils.Except ( MonadError(catchError) )
import Agda.Utils.Functor
import Agda.Utils.Lens
import Agda.Utils.List
import Agda.Utils.Maybe
import Agda.Utils.Monad
import Agda.Utils.Null
import Agda.Utils.Permutation
import Agda.Utils.Pretty hiding ((<>))
import Agda.Utils.Singleton
import Agda.Utils.Size
import Agda.Utils.Tuple

#include "undefined.h"
import Agda.Utils.Impossible

-- Composition of reified applications ------------------------------------

napps :: Expr -> [NamedArg Expr] -> TCM Expr
napps e = nelims e . map I.Apply

apps :: Expr -> [Arg Expr] -> TCM Expr
apps e = elims e . map I.Apply

-- Composition of reified eliminations ------------------------------------

nelims :: Expr -> [I.Elim' (Named_ Expr)] -> TCM Expr
nelims e [] = return e
nelims e (I.Apply arg : es) = do
  arg <- reify arg  -- This replaces the arg by _ if irrelevant
  dontShowImp <- not <$> showImplicitArguments
  let hd | notVisible arg && dontShowImp = e
         | otherwise                     = A.App noExprInfo e arg
  nelims hd es
nelims e (I.Proj d    : es) =
  nelims (A.App noExprInfo (A.Proj $ AmbQ [d]) $ defaultNamedArg e) es

elims :: Expr -> [I.Elim' Expr] -> TCM Expr
elims e = nelims e . map (fmap unnamed)

-- Omitting information ---------------------------------------------------

noExprInfo :: ExprInfo
noExprInfo = ExprRange noRange

-- Conditional reification to omit terms that are not shown --------------

reifyWhenE :: Reify i Expr => Bool -> i -> TCM Expr
reifyWhenE True  i = reify i
reifyWhenE False t = return underscore

-- Reification ------------------------------------------------------------

class Reify i a | i -> a where
    reify     ::         i -> TCM a

    --   @reifyWhen False@ should produce an 'underscore'.
    --   This function serves to reify hidden/irrelevant things.
    reifyWhen :: Bool -> i -> TCM a
    reifyWhen _ = reify

instance Reify Name Name where
    reify = return

instance Reify Expr Expr where
    reifyWhen = reifyWhenE
    reify = return

instance Reify MetaId Expr where
    reifyWhen = reifyWhenE
    reify x@(MetaId n) = liftTCM $ do
      mi  <- mvInfo <$> lookupMeta x
      let mi' = Info.MetaInfo
                 { metaRange          = getRange $ miClosRange mi
                 , metaScope          = clScope $ miClosRange mi
                 , metaNumber         = Just x
                 , metaNameSuggestion = miNameSuggestion mi
                 }
          underscore = return $ A.Underscore mi'
      ifNotM shouldReifyInteractionPoints underscore $ {- else -}
        caseMaybeM (isInteractionMeta x) underscore $ \ ii@InteractionId{} ->
          return $ A.QuestionMark mi' ii

-- Does not print with-applications correctly:
-- instance Reify DisplayTerm Expr where
--   reifyWhen = reifyWhenE
--   reify d = reifyTerm False $ dtermToTerm d

instance Reify DisplayTerm Expr where
  reifyWhen = reifyWhenE
  reify d = case d of
    DTerm v -> reifyTerm False v
    DDot  v -> reify v
    DCon c vs -> apps (A.Con (AmbQ [conName c])) =<< reify vs
    DDef f es -> elims (A.Def f) =<< reify es
    DWithApp u us vs -> do
      (e, es) <- reify (u, us)
      apps (if null es then e else A.WithApp noExprInfo e es) =<< reify vs

-- | @reifyDisplayForm f vs fallback@
--   tries to rewrite @f vs@ with a display form for @f@.
--   If successful, reifies the resulting display term,
--   otherwise, does @fallback@.
reifyDisplayForm :: QName -> I.Args -> TCM A.Expr -> TCM A.Expr
reifyDisplayForm f vs fallback = do
  ifNotM displayFormsEnabled fallback $ {- else -} do
    caseMaybeM (liftTCM $ displayForm f vs) fallback reify

-- | @reifyDisplayFormP@ tries to recursively
--   rewrite a lhs with a display form.
--
--   Note: we are not necessarily in the empty context upon entry!
reifyDisplayFormP :: A.SpineLHS -> TCM A.SpineLHS
reifyDisplayFormP lhs@(A.SpineLHS i f ps wps) =
  ifNotM displayFormsEnabled (return lhs) $ {- else -} do
    let vs = [ setHiding h $ defaultArg $ I.var i
             | (i, h) <- zip [0..] $ map getHiding ps
             ]
    -- Try to rewrite @f 0 1 2 ... |ps|-1@ to a dt.
    -- Andreas, 2014-06-11  Issue 1177:
    -- I thought we need to add the placeholders for ps to the context,
    -- because otherwise displayForm will not raise the display term
    -- and we will have variable clashes.
    -- But apparently, it has no influence...
    -- Ulf, can you add an explanation?
    md <- liftTCM $ -- addContext (replicate (length ps) "x") $
      displayForm f vs
    reportSLn "reify.display" 60 $
      "display form of " ++ show f ++ " " ++ show ps ++ " " ++ show wps ++ ":\n  " ++ show md
    case md of
      Just d  | okDisplayForm d -> do
        -- In the display term @d@, @var i@ should be a placeholder
        -- for the @i@th pattern of @ps@.
        -- Andreas, 2014-06-11:
        -- Are we sure that @d@ did not use @var i@ otherwise?
        lhs' <- displayLHS (map namedArg ps) wps d
        reportSDoc "reify.display" 70 $ do
          doc <- prettyA lhs'
          return $ vcat
            [ text "rewritten lhs to"
            , text "  lhs' = " <+> doc
            ]
        reifyDisplayFormP lhs'
      _ -> do
        reportSLn "reify.display" 70 $ "display form absent or not valid as lhs"
        return lhs
  where
    -- Andreas, 2015-05-03: Ulf, please comment on what
    -- is the idea behind okDisplayForm.
    -- Ulf, 2016-04-15: okDisplayForm should return True if the display form
    -- can serve as a valid left-hand side. That means checking that it is a
    -- defined name applied to valid lhs eliminators (projections or
    -- applications to constructor patterns).
    okDisplayForm (DWithApp d ds args) =
      okDisplayForm d && all okDisplayTerm ds  && all okToDrop args
      -- Andreas, 2016-05-03, issue #1950.
      -- We might drop trailing hidden trivial (=variable) patterns.
    okDisplayForm (DTerm (I.Def f vs)) = all okElim vs
    okDisplayForm (DDef f es)          = all okDElim es
    okDisplayForm DDot{}               = False
    okDisplayForm DCon{}               = False
    okDisplayForm DTerm{}              = False

    okDisplayTerm (DTerm v) = okTerm v
    okDisplayTerm DDot{}    = True
    okDisplayTerm DCon{}    = True
    okDisplayTerm DDef{}    = False
    okDisplayTerm _         = False

    okDElim (I.Apply v) = okDisplayTerm $ unArg v
    okDElim I.Proj{}    = True

    okToDrop arg = notVisible arg && case ignoreSharing $ unArg arg of
      I.Var _ []   -> True
      I.DontCare{} -> True  -- no matching on irrelevant things.  __IMPOSSIBLE__ anyway?
      I.Level{}    -> True  -- no matching on levels. __IMPOSSIBLE__ anyway?
      _ -> False

    okArg = okTerm . unArg

    okElim (I.Apply a) = okArg a
    okElim (I.Proj{})  = True

    okTerm (I.Var _ []) = True
    okTerm (I.Con c vs) = all okArg vs
    okTerm (I.Def x []) = isNoName $ qnameToConcrete x -- Handling wildcards in display forms
    okTerm _            = False

    -- Flatten a dt into (parentName, parentElims, withArgs).
    flattenWith :: DisplayTerm -> (QName, [I.Elim' DisplayTerm], [DisplayTerm])
    flattenWith (DWithApp d ds1 ds2) = case flattenWith d of
      (f, es, ds0) -> (f, es, ds0 ++ ds1 ++ map (DTerm . unArg) ds2)
    flattenWith (DDef f es) = (f, es, [])     -- .^ hacky, but we should only hit this when printing debug info
    flattenWith (DTerm (I.Def f es)) = (f, map (fmap DTerm) es, [])
    flattenWith _ = __IMPOSSIBLE__

    displayLHS :: [A.Pattern] -> [A.Pattern] -> DisplayTerm -> TCM A.SpineLHS
    displayLHS ps wps d = case flattenWith d of
      (f, vs, ds) -> do
        ds <- mapM termToPat ds
        vs <- mapM elimToPat vs
        return $ SpineLHS i f vs (ds ++ wps)
      where
        ci   = ConPatInfo ConPCon patNoRange

        argToPat arg = fmap unnamed <$> traverse termToPat arg
        elimToPat (I.Apply arg) = argToPat arg
        elimToPat (I.Proj d)    = return $ defaultNamedArg $ A.ProjP patNoRange $ AmbQ [d]

        termToPat :: DisplayTerm -> TCM A.Pattern

        termToPat (DTerm (I.Var n [])) = return $ case ps !!! n of
                                           Nothing -> __IMPOSSIBLE__
                                           Just p  -> p

        termToPat (DCon c vs)          = tryRecPFromConP =<< do
           A.ConP ci (AmbQ [conName c]) <$> mapM argToPat vs

        termToPat (DTerm (I.Con c vs)) = tryRecPFromConP =<< do
           A.ConP ci (AmbQ [conName c]) <$> mapM (argToPat . fmap DTerm) vs

        termToPat (DTerm (I.Def _ [])) = return $ A.WildP patNoRange
        termToPat (DDef _ [])          = return $ A.WildP patNoRange

        termToPat (DDot v)             = A.DotP patNoRange <$> termToExpr v
        termToPat v                    = A.DotP patNoRange <$> reify v -- __IMPOSSIBLE__

        len = genericLength ps

        argsToExpr = mapM (traverse termToExpr)

        -- TODO: restructure this to avoid having to repeat the code for reify
        termToExpr :: Term -> TCM A.Expr
        termToExpr v = do
          reportSLn "reify.display" 60 $ "termToExpr " ++ show v
          -- After unSpine, a Proj elimination is __IMPOSSIBLE__!
          case unSpine v of
            I.Con c vs ->
              apps (A.Con (AmbQ [conName c])) =<< argsToExpr vs
            I.Def f es -> do
              let vs = fromMaybe __IMPOSSIBLE__ $ mapM isApplyElim es
              apps (A.Def f) =<< argsToExpr vs
            I.Var n es -> do
              let vs = fromMaybe __IMPOSSIBLE__ $ mapM isApplyElim es
              -- Andreas, 2014-06-11  Issue 1177
              -- due to β-normalization in substitution,
              -- even the pattern variables @n < len@ can be
              -- applied to some args @vs@.
              e <- if n < len
                   then return $ A.patternToExpr $ ps !! n
                   else reify (I.var (n - len))
              apps e =<< argsToExpr vs
            _ -> return underscore

instance Reify Literal Expr where
  reifyWhen = reifyWhenE
  reify l = return (A.Lit l)

instance Reify Term Expr where
  reifyWhen = reifyWhenE
  reify v = reifyTerm True v

reifyTerm :: Bool -> Term -> TCM Expr
reifyTerm expandAnonDefs0 v = do
  -- Ulf 2014-07-10: Don't expand anonymous when display forms are disabled
  -- (i.e. when we don't care about nice printing)
  expandAnonDefs <- return expandAnonDefs0 `and2M` displayFormsEnabled
  v <- unSpine <$> instantiate v
  case v of
    I.Var n es   -> do
        x  <- liftTCM $ nameOfBV n `catchError` \_ -> freshName_ ("@" ++ show n)
        elims (A.Var x) =<< reify es
    I.Def x es   -> do
      let vs = fromMaybe __IMPOSSIBLE__ $ allApplyElims es
      reifyDisplayForm x vs $ reifyDef expandAnonDefs x vs
    I.Con c vs   -> do
      let x = conName c
      isR <- isGeneratedRecordConstructor x
      case isR of
        True -> do
          showImp <- showImplicitArguments
          let keep (a, v) = showImp || notHidden a
          r  <- getConstructorData x
          xs <- getRecordFieldNames r
          vs <- map unArg <$> reify vs
          return $ A.Rec noExprInfo $ map (Left . uncurry FieldAssignment . mapFst unArg) $ filter keep $ zip xs vs
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
            if np == 0 then apps h es else do
              -- Get name of first argument from type of constructor.
              -- Here, we need the reducing version of @telView@
              -- because target of constructor could be a definition
              -- expanding into a function type.  See test/succeed/NameFirstIfHidden.agda.
              TelV tel _ <- telView (defType ci)
              case genericDrop np $ telToList tel of
                -- Andreas, 2012-09-18
                -- If the first regular constructor argument is hidden,
                -- we keep the parameters to avoid confusion.
                (Dom info _ : _) | isHidden info -> do
                  let us = genericReplicate (np - n) $
                             setRelevance Relevant $ Arg info underscore
                  apps h $ us ++ es
                -- otherwise, we drop all parameters
                _ -> apps h es

--    I.Lam info b | isAbsurdBody b -> return $ A. AbsurdLam noExprInfo $ getHiding info
    I.Lam info b    -> do
      (x,e) <- reify b
      return $ A.Lam noExprInfo (DomainFree info x) e
      -- Andreas, 2011-04-07 we do not need relevance information at internal Lambda
    I.Lit l        -> reify l
    I.Level l      -> reify l
    I.Pi a b       -> case b of
        NoAbs _ b'
          | notHidden a -> uncurry (A.Fun $ noExprInfo) <$> reify (a, b')
            -- Andreas, 2013-11-11 Hidden/Instance I.Pi must be A.Pi
            -- since (a) the syntax {A} -> B or {{A}} -> B is not legal
            -- and (b) the name of the binder might matter.
            -- See issue 951 (a) and 952 (b).
          | otherwise   -> mkPi b =<< reify a
        b               -> mkPi b =<< do
          ifM (domainFree a (absBody b))
            {- then -} (pure $ Arg (domInfo a) underscore)
            {- else -} (reify a)
      where
        mkPi b (Arg info a) = do
          (x, b) <- reify b
          return $ A.Pi noExprInfo [TypedBindings noRange $ Arg info (TBind noRange [pure x] a)] b
        -- We can omit the domain type if it doesn't have any free variables
        -- and it's mentioned in the target type.
        domainFree a b = do
          df <- asks envPrintDomainFreePi
          return $ and [df, freeIn 0 b, closed a]

    I.Sort s     -> reify s
    I.MetaV x es -> do
      x' <- reify x
      elims x' =<< reify es
    I.DontCare v -> A.DontCare <$> reifyTerm expandAnonDefs v
    I.Shared p   -> reifyTerm expandAnonDefs $ derefPtr p
  where
    -- Andreas, 2012-10-20  expand a copy if not in scope
    -- to improve error messages.
    -- Don't do this if we have just expanded into a display form,
    -- otherwise we loop!
    reifyDef :: Bool -> QName -> I.Args -> TCM Expr
    reifyDef True x vs =
      ifM (not . null . inverseScopeLookupName x <$> getScope) (reifyDef' x vs) $ do
      r <- reduceDefCopy x vs
      case r of
        YesReduction _ v -> do
          reportSLn "reify.anon" 60 $ unlines
            [ "reduction on defined ident. in anonymous module"
            , "x = " ++ show x
            , "v = " ++ show v
            ]
          reify v
        NoReduction () -> do
          reportSLn "reify.anon" 60 $ unlines
            [ "no reduction on defined ident. in anonymous module"
            , "x  = " ++ show x
            , "vs = " ++ show vs
            ]
          reifyDef' x vs
    reifyDef _ x vs = reifyDef' x vs

    reifyDef' :: QName -> I.Args -> TCM Expr
    reifyDef' x@(QName _ name) vs = do
      -- We should drop this many arguments from the local context.
      n <- getDefFreeVars x
      -- If the definition is not (yet) in the signature,
      -- we just do the obvious.
      let fallback = apps (A.Def x) =<< reify (drop n vs)
      caseMaybeM (tryMaybe $ getConstInfo x) fallback $ \ defn -> do
      let def = theDef defn

      -- Check if we have an absurd lambda.
      case def of
       Function{ funCompiled = Just Fail, funClauses = [cl] }
                | isAbsurdLambdaName x -> do
                  -- get hiding info from last pattern, which should be ()
                  let h = getHiding $ last (clausePats cl)
                  apps (A.AbsurdLam noExprInfo h) =<< reify vs

      -- Otherwise (no absurd lambda):
       _ -> do

        -- Andrea(s), 2016-07-06
        -- Extended lambdas are not considered to be projection like,
        -- as they are mutually recursive with their parent.
        -- Thus we do not have to consider padding them.

        -- Check whether we have an extended lambda and display forms are on.
        df <- displayFormsEnabled
        let extLam = case def of
             Function{ funExtLam = Just{}, funProjection = Just{} } -> __IMPOSSIBLE__
             Function{ funExtLam = Just (ExtLamInfo h nh) } ->
               let npars = h + nh
               -- Andreas, 2016-07-06 Issue #2047
               -- Check that we can actually drop the parameters
               -- of the extended lambda.
               -- This is only possible if the first @npars@ patterns
               -- are variable patterns.
               -- If we encounter a non-variable pattern, fall back
               -- to printing without nice extended lambda syntax.
                   ps = map namedArg $ take npars $ namedClausePats $
                     fromMaybe __IMPOSSIBLE__ $ headMaybe (defClauses defn)
                   isVarP I.VarP{} = True
                   isVarP _ = False
               in  if all isVarP ps then Just npars else Nothing
             _ -> Nothing
        case extLam of
          Just pars | df -> reifyExtLam x pars (defClauses defn) vs

        -- Otherwise (ordinay function call):
          _ -> do

           (pad, nvs :: [NamedArg Term]) <- case def of

            Function{ funProjection = Just Projection{ projIndex = np } } | np > 0 -> do
              -- This is tricky:
              --  * getDefFreeVars x tells us how many arguments
              --    are part of the local context
              --  * some of those arguments might have been dropped
              --    due to projection likeness
              --  * when showImplicits is on we'd like to see the dropped
              --    projection arguments

              TelV tel _ <- telViewUpTo np (defType defn)
              let (as, rest) = splitAt (np - 1) $ telToList tel
                  dom = fromMaybe __IMPOSSIBLE__ $ headMaybe rest

              -- These are the dropped projection arguments
              scope <- getScope
              let underscore = A.Underscore $ Info.emptyMetaInfo { metaScope = scope }
              let pad = for as $ \ (Dom ai _) -> Arg ai underscore

              -- Now pad' ++ vs' = drop n (pad ++ vs)
              let pad' = drop n pad
                  vs'  = drop (max 0 (n - size pad)) vs
              -- Andreas, 2012-04-21: get rid of hidden underscores {_}
              -- Keep non-hidden arguments of the padding
              showImp <- showImplicitArguments
              return (filter visible pad',
                if not (null pad) && showImp && notVisible (last pad)
                   then nameFirstIfHidden dom vs'
                   else map (fmap unnamed) vs')

            -- If it is not a projection(-like) function, we need no padding.
            _ -> return ([], map (fmap unnamed) $ drop n vs)
           let hd = foldl' (\ e a -> A.App noExprInfo e (fmap unnamed a)) (A.Def x) pad
           napps hd =<< reify nvs

    -- Andreas, 2016-07-06 Issue #2047

    -- With parameter refinement, the "parameter" patterns of an extended
    -- lambda can now be different from variable patterns.  If we just drop
    -- them (plus the associated arguments to the extended lambda), we produce
    -- something

    -- * that violates internal invariants.  In particular, the permutation
    --   dbPatPerm from the patterns to the telescope can no longer be
    --   computed.  (And in fact, dropping from the start of the telescope is
    --   just plainly unsound then.)

    -- * prints the wrong thing (old fix for #2047)

    -- What we do now, is more sound, although not entirely satisfying:
    -- When the "parameter" patterns of an external lambdas are not variable
    -- patterns, we fall back to printing the internal function created for the
    -- extended lambda, instead trying to construct the nice syntax.

    reifyExtLam :: QName -> Int -> [I.Clause] -> [Arg Term] -> TCM Expr
    reifyExtLam x npars cls vs = do
      reportSLn "reify.def" 10 $ "reifying extended lambda with definition: x = " ++ show x
      -- As extended lambda clauses live in the top level, we add the whole
      -- section telescope to the number of parameters.
      toppars <- size <$> do lookupSection $ qnameModule x
      let (pars, rest) = splitAt (toppars + npars) vs
      -- Since we applying the clauses to the parameters,
      -- we do not need to drop their initial "parameter" patterns
      -- (this is taken care of by @apply@).
      cls <- mapM (reify . NamedClause x False . (`apply` pars)) cls
      let cx    = nameConcrete $ qnameName x
          dInfo = mkDefInfo cx noFixity' PublicAccess ConcreteDef (getRange x)
      apps (A.ExtendedLam noExprInfo dInfo x cls) =<< reify rest

-- | @nameFirstIfHidden (x:a) ({e} es) = {x = e} es@
nameFirstIfHidden :: Dom (ArgName, t) -> [Arg a] -> [NamedArg a]
nameFirstIfHidden dom (Arg info e : es) | isHidden info =
  Arg info (Named (Just $ unranged $ fst $ unDom dom) e) :
  map (fmap unnamed) es
nameFirstIfHidden _ es =
  map (fmap unnamed) es

instance Reify i a => Reify (Named n i) (Named n a) where
  reify = traverse reify
  reifyWhen b = traverse (reifyWhen b)

-- | Skip reification of implicit and irrelevant args if option is off.
instance (Reify i a) => Reify (Arg i) (Arg a) where
  reify (Arg info i) = Arg info <$> (flip reifyWhen i =<< condition)
    where condition = (return (argInfoHiding info /= Hidden) `or2M` showImplicitArguments)
              `and2M` (return (argInfoRelevance info /= Irrelevant) `or2M` showIrrelevantArguments)
  reifyWhen b i = traverse (reifyWhen b) i


data NamedClause = NamedClause QName Bool I.Clause
  -- ^ Also tracks whether module parameters should be dropped from the patterns.

instance Reify ClauseBody RHS where
  reify NoBody     = return AbsurdRHS
  reify (Body v)   = RHS <$> reify v
  reify (Bind b)   = reify $ absBody b  -- the variables should already be bound

-- The Monoid instance for Data.Map doesn't require that the values are a
-- monoid.
newtype MonoidMap k v = MonoidMap { unMonoidMap :: Map.Map k v }

instance (Ord k, Monoid v) => Semigroup (MonoidMap k v) where
  MonoidMap m1 <> MonoidMap m2 = MonoidMap (Map.unionWith mappend m1 m2)

instance (Ord k, Monoid v) => Monoid (MonoidMap k v) where
  mempty = MonoidMap Map.empty
  mappend = (<>)

-- | Removes implicit arguments that are not needed, that is, that don't bind
--   any variables that are actually used and doesn't do pattern matching.
--   Doesn't strip any arguments that were written explicitly by the user.
stripImplicits :: ([NamedArg A.Pattern], [A.Pattern]) ->
                  TCM ([NamedArg A.Pattern], [A.Pattern])
stripImplicits (ps, wps) = do          -- v if show-implicit we don't need the names
  ifM showImplicitArguments (return (map (unnamed . namedThing <$>) ps, wps)) $ do
    reportSLn "reify.implicit" 30 $ unlines
      [ "stripping implicits"
      , "  ps   = " ++ show ps
      , "  wps  = " ++ show wps
      ]
    let allps       = ps ++ map defaultNamedArg wps
        sps         = blankDots $ strip allps
        (ps', wps') = splitAt (length sps - length wps) sps
    reportSLn "reify.implicit" 30 $ unlines
      [ "  ps'  = " ++ show ps'
      , "  wps' = " ++ show (map namedArg wps')
      ]
    return (ps', map namedArg wps')
    where
      -- Replace variables in dot patterns by an underscore _ if they are hidden
      -- in the pattern. This is slightly nicer than making the implicts explicit.
      blankDots ps = blank (varsBoundIn ps) ps

      strip ps = stripArgs True ps
        where
          stripArgs _ [] = []
          stripArgs fixedPos (a : as) =
            if canStrip a
            then if   all canStrip $ takeWhile isUnnamedHidden as
                 then stripArgs False as
                 else let a' = fmap ($> A.WildP (Info.PatRange $ getRange a)) a
                      in  stripName fixedPos a' : stripArgs True as
            else stripName fixedPos (stripArg a) : stripArgs True as

          stripName True  = fmap (unnamed . namedThing)
          stripName False = id

          canStrip a = and
            [ notVisible a
            , getOrigin a /= UserWritten
            , varOrDot (namedArg a)
            ]

          isUnnamedHidden x = notVisible x && nameOf (unArg x) == Nothing

          stripArg a = fmap (fmap stripPat) a

          stripPat p = case p of
            A.VarP _      -> p
            A.ConP i c ps -> A.ConP i c $ stripArgs True ps
            A.ProjP _ _   -> p
            A.DefP _ _ _  -> p
            A.DotP _ e    -> p
            A.WildP _     -> p
            A.AbsurdP _   -> p
            A.LitP _      -> p
            A.AsP i x p   -> A.AsP i x $ stripPat p
            A.PatternSynP _ _ _ -> __IMPOSSIBLE__ -- p
            A.RecP i fs   -> A.RecP i $ map (fmap stripPat) fs  -- TODO Andreas: is this right?

          varOrDot A.VarP{}      = True
          varOrDot A.WildP{}     = True
          varOrDot A.DotP{}      = True
          varOrDot (A.ConP cpi _ ps) | patOrigin cpi == ConPImplicit
                                 = all varOrDot $ map namedArg ps
          varOrDot _             = False

-- | @blank bound x@ replaces all variables in @x@ that are not in @bound@ by
--   an underscore @_@. It is used for printing dot patterns: we don't want to
--   make implicit variables explicit, so we blank them out in the dot patterns
--   instead (this is fine since dot patterns can be inferred anyway).
class BlankVars a where
  blank :: Set Name -> a -> a

instance BlankVars a => BlankVars (Arg a) where
  blank bound = fmap $ blank bound

instance BlankVars a => BlankVars (Named s a) where
  blank bound = fmap $ blank bound

instance BlankVars a => BlankVars [a] where
  blank bound = fmap $ blank bound

instance (BlankVars a, BlankVars b) => BlankVars (a, b) where
  blank bound (x, y) = (blank bound x, blank bound y)

instance (BlankVars a, BlankVars b) => BlankVars (Either a b) where
  blank bound (Left x)  = Left $ blank bound x
  blank bound (Right y) = Right $ blank bound y

instance BlankVars A.NamedDotPattern where
  blank bound = id

instance BlankVars A.Clause where
  blank bound (A.Clause lhs namedDots rhs [] ca) =
    let bound' = varsBoundIn lhs `Set.union` bound
    in  A.Clause (blank bound' lhs)
                 (blank bound' namedDots)
                 (blank bound' rhs) [] ca
  blank bound (A.Clause lhs namedDots rhs (_:_) ca) = __IMPOSSIBLE__

instance BlankVars A.LHS where
  blank bound (A.LHS i core wps) = uncurry (A.LHS i) $ blank bound (core, wps)

instance BlankVars A.LHSCore where
  blank bound (A.LHSHead f ps) = A.LHSHead f $ blank bound ps
  blank bound (A.LHSProj p b ps) = uncurry (A.LHSProj p) $ blank bound (b, ps)

instance BlankVars A.Pattern where
  blank bound p = case p of
    A.VarP _      -> p   -- do not blank pattern vars
    A.ConP c i ps -> A.ConP c i $ blank bound ps
    A.ProjP _ _   -> p
    A.DefP i f ps -> A.DefP i f $ blank bound ps
    A.DotP i e    -> A.DotP i $ blank bound e
    A.WildP _     -> p
    A.AbsurdP _   -> p
    A.LitP _      -> p
    A.AsP i n p   -> A.AsP i n $ blank bound p
    A.PatternSynP _ _ _ -> __IMPOSSIBLE__
    A.RecP i fs   -> A.RecP i $ blank bound fs

instance BlankVars A.Expr where
  blank bound e = case e of
    A.ScopedExpr i e       -> A.ScopedExpr i $ blank bound e
    A.Var x                -> if x `Set.member` bound then e
                              else A.Underscore emptyMetaInfo
    A.Def _                -> e
    A.Proj _               -> e
    A.Con _                -> e
    A.Lit _                -> e
    A.QuestionMark{}       -> e
    A.Underscore _         -> e
    A.App i e1 e2          -> uncurry (A.App i) $ blank bound (e1, e2)
    A.WithApp i e es       -> uncurry (A.WithApp i) $ blank bound (e, es)
    A.Lam i b e            -> let bound' = varsBoundIn b `Set.union` bound
                              in  A.Lam i (blank bound b) (blank bound' e)
    A.AbsurdLam _ _        -> e
    A.ExtendedLam i d f cs -> A.ExtendedLam i d f $ blank bound cs
    A.Pi i tel e           -> let bound' = varsBoundIn tel `Set.union` bound
                              in  uncurry (A.Pi i) $ blank bound' (tel, e)
    A.Fun i a b            -> uncurry (A.Fun i) $ blank bound (a, b)
    A.Set _ _              -> e
    A.Prop _               -> e
    A.Let _ _ _            -> __IMPOSSIBLE__
    A.Rec i es             -> A.Rec i $ blank bound es
    A.RecUpdate i e es     -> uncurry (A.RecUpdate i) $ blank bound (e, es)
    A.ETel _               -> __IMPOSSIBLE__
    A.QuoteGoal {}         -> __IMPOSSIBLE__
    A.QuoteContext {}      -> __IMPOSSIBLE__
    A.Quote {}             -> __IMPOSSIBLE__
    A.QuoteTerm {}         -> __IMPOSSIBLE__
    A.Unquote {}           -> __IMPOSSIBLE__
    A.Tactic {}            -> __IMPOSSIBLE__
    A.DontCare v           -> A.DontCare $ blank bound v
    A.PatternSyn {}        -> e
    A.Macro {}             -> e

instance BlankVars a => BlankVars (FieldAssignment' a) where
  blank bound = over exprFieldA (blank bound)

instance BlankVars A.ModuleName where
  blank bound = id

instance BlankVars RHS where
  blank bound (RHS e)                = RHS $ blank bound e
  blank bound AbsurdRHS              = AbsurdRHS
  blank bound (WithRHS _ es clauses) = __IMPOSSIBLE__ -- NZ
  blank bound (RewriteRHS xes rhs _) = __IMPOSSIBLE__ -- NZ

instance BlankVars A.LamBinding where
  blank bound b@A.DomainFree{} = b
  blank bound (A.DomainFull bs) = A.DomainFull $ blank bound bs

instance BlankVars TypedBindings where
  blank bound (TypedBindings r bs) = TypedBindings r $ blank bound bs

instance BlankVars TypedBinding where
  blank bound (TBind r n e) = TBind r n $ blank bound e
  blank bound (TLet _ _)    = __IMPOSSIBLE__ -- Since the internal syntax has no let bindings left

class Binder a where
  varsBoundIn :: a -> Set Name

instance Binder A.LHS where
  varsBoundIn (A.LHS _ core ps) = varsBoundIn (core, ps)

instance Binder A.LHSCore where
  varsBoundIn (A.LHSHead _ ps)   = varsBoundIn ps
  varsBoundIn (A.LHSProj _ b ps) = varsBoundIn (b, ps)

instance Binder A.Pattern where
  varsBoundIn p = case p of
    A.VarP x             -> if show x == "()" then empty else singleton x
    A.ConP _ _ ps        -> varsBoundIn ps
    A.ProjP{}            -> empty
    A.DefP _ _ ps        -> varsBoundIn ps
    A.WildP{}            -> empty
    A.AsP _ _ p          -> varsBoundIn p
    A.DotP{}             -> empty
    A.AbsurdP{}          -> empty
    A.LitP{}             -> empty
    A.PatternSynP _ _ ps -> varsBoundIn ps
    A.RecP _ fs          -> varsBoundIn fs

instance Binder A.LamBinding where
  varsBoundIn (A.DomainFree _ x) = singleton x
  varsBoundIn (A.DomainFull b)   = varsBoundIn b

instance Binder TypedBindings where
  varsBoundIn (TypedBindings _ b) = varsBoundIn b

instance Binder TypedBinding where
  varsBoundIn (TBind _ xs _) = varsBoundIn xs
  varsBoundIn (TLet _ bs)    = varsBoundIn bs

instance Binder LetBinding where
  varsBoundIn (LetBind _ _ x _ _) = singleton x
  varsBoundIn (LetPatBind _ p _)  = varsBoundIn p
  varsBoundIn LetApply{}          = empty
  varsBoundIn LetOpen{}           = empty
  varsBoundIn LetDeclaredVariable{} = empty

instance Binder a => Binder (FieldAssignment' a) where
  varsBoundIn = varsBoundIn . (^. exprFieldA)

instance Binder a => Binder (Arg a) where
  varsBoundIn = varsBoundIn . unArg

instance Binder a => Binder (Named x a) where
  varsBoundIn = varsBoundIn . namedThing

instance Binder (WithHiding Name) where
  varsBoundIn (WithHiding _ x) = singleton x

instance Binder a => Binder [a] where
  varsBoundIn xs = Set.unions $ map varsBoundIn xs

instance (Binder a, Binder b) => Binder (a, b) where
  varsBoundIn (x, y) = varsBoundIn x `Set.union` varsBoundIn y


-- | Assumes that pattern variables have been added to the context already.
--   Picks pattern variable names from context.
reifyPatterns :: MonadTCM tcm => [NamedArg I.DeBruijnPattern] -> tcm [NamedArg A.Pattern]
reifyPatterns = mapM $ stripNameFromExplicit <.> traverse (traverse reifyPat)
  where
    stripNameFromExplicit :: NamedArg p -> NamedArg p
    stripNameFromExplicit a
      | getHiding a == NotHidden = fmap (unnamed . namedThing) a
      | otherwise                = a

    reifyPat :: MonadTCM tcm => I.DeBruijnPattern -> tcm A.Pattern
    reifyPat p = do
     liftTCM $ reportSLn "reify.pat" 80 $ "reifying pattern " ++ show p
     case p of
      I.VarP x | isAbsurdPatternName (dbPatVarName x)
               -> return $ A.AbsurdP patNoRange    -- HACK
      I.VarP x -> liftTCM $ A.VarP <$> nameOfBV (dbPatVarIndex x)
      I.DotP v -> do
        t <- liftTCM $ reify v
        return $ A.DotP patNoRange t
      I.LitP l  -> return $ A.LitP l
      I.ProjP d -> return $ A.ProjP patNoRange $ AmbQ [d]
      I.ConP c cpi ps -> do
        liftTCM $ reportSLn "reify.pat" 60 $ "reifying pattern " ++ show p
        tryRecPFromConP =<< do A.ConP ci (AmbQ [conName c]) <$> reifyPatterns ps
        where
          ci = ConPatInfo origin patNoRange
          origin = fromMaybe ConPCon $ I.conPRecord cpi

-- | If the record constructor is generated or the user wrote a record pattern,
--   turn constructor pattern into record pattern.
--   Otherwise, keep constructor pattern.
tryRecPFromConP :: MonadTCM tcm => A.Pattern -> tcm A.Pattern
tryRecPFromConP p = do
  let fallback = return p
  case p of
    A.ConP ci (AmbQ [c]) ps -> do
        caseMaybeM (liftTCM $ isRecordConstructor c) fallback $ \ (r, def) -> do
          -- If the record constructor is generated or the user wrote a record pattern,
          -- print record pattern.
          -- Otherwise, print constructor pattern.
          if recNamedCon def && patOrigin ci /= ConPRec then fallback else do
            fs <- liftTCM $ getRecordFieldNames r
            unless (length fs == length ps) __IMPOSSIBLE__
            return $ A.RecP patNoRange $ zipWith mkFA fs ps
        where
          mkFA ax nap = FieldAssignment (unArg ax) (namedArg nap)
    _ -> __IMPOSSIBLE__

instance Reify (QNamed I.Clause) A.Clause where
  reify (QNamed f cl) = reify (NamedClause f True cl)

instance Reify NamedClause A.Clause where
  reify (NamedClause f toDrop cl@(I.Clause _ tel ps body _ catchall)) = addContext tel $ do
    reportSLn "reify.clause" 60 $ "reifying NamedClause, cl = " ++ show cl
    ps  <- reifyPatterns ps
    lhs <- liftTCM $ reifyDisplayFormP $ SpineLHS info f ps [] -- LHS info (LHSHead f ps) []
    -- Unless @toDrop@ we have already dropped the module patterns from the clauses
    -- (e.g. for extended lambdas).
    lhs <- if not toDrop then return lhs else do
      nfv <- getDefFreeVars f `catchError` \_ -> return 0
      return $ dropParams nfv lhs
    lhs <- stripImps lhs
    reportSLn "reify.clause" 60 $ "reifying NamedClause, lhs = " ++ show lhs
    rhs <- reify $ renameP (reverseP perm) <$> body
    reportSLn "reify.clause" 60 $ "reifying NamedClause, rhs = " ++ show rhs
    let result = A.Clause (spineToLhs lhs) [] rhs [] catchall
    reportSLn "reify.clause" 60 $ "reified NamedClause, result = " ++ show result
    return result
    where
      info = LHSRange noRange
      perm = fromMaybe __IMPOSSIBLE__ $ dbPatPerm ps

      dropParams n (SpineLHS i f ps wps) = SpineLHS i f (genericDrop n ps) wps
      stripImps (SpineLHS i f ps wps) = do
        (ps, wps) <- stripImplicits (ps, wps)
        return $ SpineLHS i f ps wps

instance Reify Type Expr where
    reifyWhen = reifyWhenE
    reify (I.El _ t) = reify t

instance Reify Sort Expr where
    reifyWhen = reifyWhenE
    reify s = do
      s <- instantiateFull s
      case s of
        I.Type (I.Max [])                -> return $ A.Set noExprInfo 0
        I.Type (I.Max [I.ClosedLevel n]) -> return $ A.Set noExprInfo n
        I.Type a -> do
          a <- reify a
          return $ A.App noExprInfo (A.Set noExprInfo 0) (defaultNamedArg a)
        I.Prop       -> return $ A.Prop noExprInfo
        I.Inf       -> A.Var <$> freshName_ ("Setω" :: String)
        I.SizeUniv  -> do
          I.Def sizeU [] <- primSizeUniv
          return $ A.Def sizeU
        I.DLub s1 s2 -> do
          lub <- freshName_ ("dLub" :: String) -- TODO: hack
          (e1,e2) <- reify (s1, I.Lam defaultArgInfo $ fmap Sort s2)
          let app x y = A.App noExprInfo x (defaultNamedArg y)
          return $ A.Var lub `app` e1 `app` e2

instance Reify Level Expr where
  reifyWhen = reifyWhenE
  reify l = reify =<< reallyUnLevelView l

instance (Free i, Reify i a) => Reify (Abs i) (Name, a) where
  reify (NoAbs x v) = (,) <$> freshName_ x <*> reify v
  reify (Abs s v) = do

    -- If the bound variable is free in the body, then the name "_" is
    -- replaced by "z".
    s <- return $ if isUnderscore s && 0 `freeIn` v then "z" else s

    x <- freshName_ s
    e <- addContext' x -- type doesn't matter
         $ reify v
    return (x,e)

instance Reify I.Telescope A.Telescope where
  reify EmptyTel = return []
  reify (ExtendTel arg tel) = do
    Arg info e <- reify arg
    (x,bs)  <- reify tel
    let r = getRange e
    return $ TypedBindings r (Arg info (TBind r [pure x] e)) : bs

instance Reify i a => Reify (Dom i) (Arg a) where
    reify (Dom info i) = Arg info <$> reify i

instance Reify i a => Reify (I.Elim' i) (I.Elim' a) where
  reify = traverse reify
  reifyWhen b = traverse (reifyWhen b)

instance Reify i a => Reify [i] [a] where
  reify = traverse reify
  reifyWhen b = traverse (reifyWhen b)

instance (Reify i1 a1, Reify i2 a2) => Reify (i1,i2) (a1,a2) where
    reify (x,y) = (,) <$> reify x <*> reify y

instance (Reify i1 a1, Reify i2 a2, Reify i3 a3) => Reify (i1,i2,i3) (a1,a2,a3) where
    reify (x,y,z) = (,,) <$> reify x <*> reify y <*> reify z

instance (Reify i1 a1, Reify i2 a2, Reify i3 a3, Reify i4 a4) => Reify (i1,i2,i3,i4) (a1,a2,a3,a4) where
    reify (x,y,z,w) = (,,,) <$> reify x <*> reify y <*> reify z <*> reify w
