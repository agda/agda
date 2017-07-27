{-# LANGUAGE CPP                        #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE NondecreasingIndentation   #-}
{-# LANGUAGE TypeFamilies               #-}  -- for type equality ~
{-# LANGUAGE UndecidableInstances       #-}

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

import Data.Foldable (Foldable, foldMap)
import Data.List hiding (null, sort)
import qualified Data.Map as Map
import Data.Maybe
import Data.Semigroup (Semigroup, Monoid, (<>), mempty, mappend)
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Traversable (Traversable, traverse, mapM)
import qualified Data.Traversable as Trav

import Agda.Syntax.Literal
import Agda.Syntax.Position
import Agda.Syntax.Common
import Agda.Syntax.Fixity
import Agda.Syntax.Concrete (FieldAssignment'(..), exprFieldA)
import Agda.Syntax.Info as Info
import Agda.Syntax.Abstract as A
import Agda.Syntax.Abstract.Pattern ( foldAPattern )
import Agda.Syntax.Abstract.Pretty
import Agda.Syntax.Internal as I
import Agda.Syntax.Internal.Pattern as I
import Agda.Syntax.Scope.Base (isNameInScope, inverseScopeLookupName)

import Agda.TypeChecking.Monad
import Agda.TypeChecking.Monad.Builtin
import Agda.TypeChecking.Reduce
import {-# SOURCE #-} Agda.TypeChecking.Records
import Agda.TypeChecking.CompiledClause (CompiledClauses'(Fail))
import Agda.TypeChecking.DisplayForm
import Agda.TypeChecking.Level
import {-# SOURCE #-} Agda.TypeChecking.Datatypes
import Agda.TypeChecking.Free
import Agda.TypeChecking.Substitute
import Agda.TypeChecking.Telescope
import Agda.TypeChecking.DropArgs

import Agda.Interaction.Options ( optPostfixProjections )

import Agda.Utils.Except ( MonadError(catchError) )
import Agda.Utils.Function
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

-- | Drops hidden arguments unless --show-implicit.
napps :: Expr -> [NamedArg Expr] -> TCM Expr
napps e = nelims e . map I.Apply

-- | Drops hidden arguments unless --show-implicit.
apps :: Expr -> [Arg Expr] -> TCM Expr
apps e = elims e . map I.Apply

-- Composition of reified eliminations ------------------------------------

-- | Drops hidden arguments unless --show-implicit.
nelims :: Expr -> [I.Elim' (Named_ Expr)] -> TCM Expr
nelims e [] = return e
nelims e (I.IApply x y r : es) =
  nelims (A.App noExprInfo e $ defaultArg r) es
nelims e (I.Apply arg : es) = do
  arg <- reify arg  -- This replaces the arg by _ if irrelevant
  dontShowImp <- not <$> showImplicitArguments
  let hd | notVisible arg && dontShowImp = e
         | otherwise                     = A.App noExprInfo e arg
  nelims hd es
nelims e (I.Proj o@ProjPrefix d  : es) =
  nelims (A.App noExprInfo (A.Proj o $ AmbQ [d]) $ defaultNamedArg e) es
nelims e (I.Proj o d  : es) =
  nelims (A.App noExprInfo e (defaultNamedArg $ A.Proj o $ AmbQ [d])) es

-- | Drops hidden arguments unless --show-implicit.
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
      b <- asks envPrintMetasBare
      mi  <- mvInfo <$> lookupMeta x
      let mi' = Info.MetaInfo
                 { metaRange          = getRange $ miClosRange mi
                 , metaScope          = clScope $ miClosRange mi
                 , metaNumber         = if b then Nothing else Just x
                 , metaNameSuggestion = if b then "" else miNameSuggestion mi
                 }
          underscore = return $ A.Underscore mi'
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
    DCon c ci vs -> apps (A.Con (AmbQ [conName c])) =<< reify vs
    DDef f es -> elims (A.Def f) =<< reify es
    DWithApp u us es0 -> do
      (e, es) <- reify (u, us)
      elims (if null es then e else A.WithApp noExprInfo e es) =<< reify es0

-- | @reifyDisplayForm f vs fallback@
--   tries to rewrite @f vs@ with a display form for @f@.
--   If successful, reifies the resulting display term,
--   otherwise, does @fallback@.
reifyDisplayForm :: QName -> I.Elims -> TCM A.Expr -> TCM A.Expr
reifyDisplayForm f es fallback = do
  ifNotM displayFormsEnabled fallback $ {- else -} do
    caseMaybeM (liftTCM $ displayForm f es) fallback reify

-- | @reifyDisplayFormP@ tries to recursively
--   rewrite a lhs with a display form.
--
--   Note: we are not necessarily in the empty context upon entry!
reifyDisplayFormP :: A.SpineLHS -> TCM A.SpineLHS
reifyDisplayFormP lhs@(A.SpineLHS i f ps wps) =
  ifNotM displayFormsEnabled (return lhs) $ {- else -} do
    -- Try to rewrite @f 0 1 2 ... |ps|-1@ to a dt.
    -- Andreas, 2014-06-11  Issue 1177:
    -- I thought we need to add the placeholders for ps to the context,
    -- because otherwise displayForm will not raise the display term
    -- and we will have variable clashes.
    -- But apparently, it has no influence...
    -- Ulf, can you add an explanation?
    md <- liftTCM $ -- addContext (replicate (length ps) "x") $
      displayForm f $ zipWith (\ p i -> I.Apply $ p $> I.var i) ps [0..]
    reportSLn "reify.display" 60 $
      "display form of " ++ prettyShow f ++ " " ++ show ps ++ " " ++ show wps ++ ":\n  " ++ show md
    case md of
      Just d  | okDisplayForm d -> do
        -- In the display term @d@, @var i@ should be a placeholder
        -- for the @i@th pattern of @ps@.
        -- Andreas, 2014-06-11:
        -- Are we sure that @d@ did not use @var i@ otherwise?
        lhs' <- displayLHS ps wps d
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
    okDisplayForm :: DisplayTerm -> Bool
    okDisplayForm (DWithApp d ds es) =
      okDisplayForm d && all okDisplayTerm ds  && all okToDropE es
      -- Andreas, 2016-05-03, issue #1950.
      -- We might drop trailing hidden trivial (=variable) patterns.
    okDisplayForm (DTerm (I.Def f vs)) = all okElim vs
    okDisplayForm (DDef f es)          = all okDElim es
    okDisplayForm DDot{}               = False
    okDisplayForm DCon{}               = False
    okDisplayForm DTerm{}              = False

    okDisplayTerm :: DisplayTerm -> Bool
    okDisplayTerm (DTerm v) = okTerm v
    okDisplayTerm DDot{}    = True
    okDisplayTerm DCon{}    = True
    okDisplayTerm DDef{}    = False
    okDisplayTerm _         = False

    okDElim :: Elim' DisplayTerm -> Bool
    okDElim (I.IApply x y r) = okDisplayTerm r
    okDElim (I.Apply v) = okDisplayTerm $ unArg v
    okDElim I.Proj{}    = True

    okToDropE :: Elim' Term -> Bool
    okToDropE (I.Apply v) = okToDrop v
    okToDropE I.Proj{}    = False
    okToDropE (I.IApply x y r) = False

    okToDrop :: Arg I.Term -> Bool
    okToDrop arg = notVisible arg && case ignoreSharing $ unArg arg of
      I.Var _ []   -> True
      I.DontCare{} -> True  -- no matching on irrelevant things.  __IMPOSSIBLE__ anyway?
      I.Level{}    -> True  -- no matching on levels. __IMPOSSIBLE__ anyway?
      _ -> False

    okArg :: Arg I.Term -> Bool
    okArg = okTerm . unArg

    okElim :: Elim' I.Term -> Bool
    okElim (I.IApply x y r) = okTerm r
    okElim (I.Apply a) = okArg a
    okElim (I.Proj{})  = True

    okTerm :: I.Term -> Bool
    okTerm (I.Var _ []) = True
    okTerm (I.Con c ci vs) = all okArg vs
    okTerm (I.Def x []) = isNoName $ qnameToConcrete x -- Handling wildcards in display forms
    okTerm _            = False

    -- Flatten a dt into (parentName, parentElims, withArgs).
    flattenWith :: DisplayTerm -> (QName, [I.Elim' DisplayTerm], [I.Elim' DisplayTerm])
    flattenWith (DWithApp d ds1 es2) =
      let (f, es, ds0) = flattenWith d
      in  (f, es, ds0 ++ map (I.Apply . defaultArg) ds1 ++ map (fmap DTerm) es2)
    flattenWith (DDef f es) = (f, es, [])     -- .^ hacky, but we should only hit this when printing debug info
    flattenWith (DTerm (I.Def f es)) = (f, map (fmap DTerm) es, [])
    flattenWith _ = __IMPOSSIBLE__

    displayLHS :: [NamedArg A.Pattern] -> [A.Pattern] -> DisplayTerm -> TCM A.SpineLHS
    displayLHS ps wps d = do
        let (f, vs, es) = flattenWith d
        ds <- mapM (namedArg <.> elimToPat) es
        vs <- mapM elimToPat vs
        return $ SpineLHS i f vs (ds ++ wps)
      where
        argToPat :: Arg DisplayTerm -> TCM (NamedArg A.Pattern)
        argToPat arg = traverse termToPat arg

        elimToPat :: I.Elim' DisplayTerm -> TCM (NamedArg A.Pattern)
        elimToPat (I.IApply _ _ r) = argToPat (Arg defaultArgInfo r)
        elimToPat (I.Apply arg) = argToPat arg
        elimToPat (I.Proj o d)  = return $ defaultNamedArg $ A.ProjP patNoRange o $ AmbQ [d]

        termToPat :: DisplayTerm -> TCM (Named_ A.Pattern)

        termToPat (DTerm (I.Var n [])) = return $ unArg $ fromMaybe __IMPOSSIBLE__ $ ps !!! n

        termToPat (DCon c ci vs)          = fmap unnamed <$> tryRecPFromConP =<< do
           A.ConP (ConPatInfo ci patNoRange) (AmbQ [conName c]) <$> mapM argToPat vs

        termToPat (DTerm (I.Con c ci vs)) = fmap unnamed <$> tryRecPFromConP =<< do
           A.ConP (ConPatInfo ci patNoRange) (AmbQ [conName c]) <$> mapM (argToPat . fmap DTerm) vs

        termToPat (DTerm (I.Def _ [])) = return $ unnamed $ A.WildP patNoRange
        termToPat (DDef _ [])          = return $ unnamed $ A.WildP patNoRange

        -- Currently we don't keep track of the origin of a dot pattern in the internal syntax,
        -- so here we give __IMPOSSIBLE__. This is only used for printing purposes, the origin
        -- should not be used anyway after this point.
        -- Andreas, 2017-02-14: This crashes with -v 100.
        -- termToPat (DDot v)             = A.DotP patNoRange __IMPOSSIBLE__ <$> termToExpr v
        -- termToPat v                    = A.DotP patNoRange __IMPOSSIBLE__ <$> reify v -- __IMPOSSIBLE__
        termToPat (DDot v)             = unnamed . A.DotP patNoRange Inserted <$> termToExpr v
        termToPat v                    = unnamed . A.DotP patNoRange Inserted <$> reify v

        len = length ps

        argsToExpr :: I.Args -> TCM [Arg A.Expr]
        argsToExpr = mapM (traverse termToExpr)

        -- TODO: restructure this to avoid having to repeat the code for reify
        termToExpr :: Term -> TCM A.Expr
        termToExpr v = do
          reportSLn "reify.display" 60 $ "termToExpr " ++ show v
          -- After unSpine, a Proj elimination is __IMPOSSIBLE__!
          case unSpine v of
            I.Con c ci vs ->
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
                   then return $ A.patternToExpr $ namedArg $ ps !! n
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
  metasBare <- asks envPrintMetasBare
  -- Ulf 2014-07-10: Don't expand anonymous when display forms are disabled
  -- (i.e. when we don't care about nice printing)
  expandAnonDefs <- return expandAnonDefs0 `and2M` displayFormsEnabled
  -- Andreas, 2016-07-21 if --postfix-projections
  -- then we print system-generated projections as postfix, else prefix.
  havePfp <- optPostfixProjections <$> pragmaOptions
  let pred = if havePfp then (== ProjPrefix) else (/= ProjPostfix)
  v <- ignoreSharing <$> instantiate v
  case applyUnless metasBare (unSpine' pred) v of
    I.Var n es   -> do
        x  <- liftTCM $ nameOfBV n `catchError` \_ -> freshName_ ("@" ++ show n)
        elims (A.Var x) =<< reify es
    I.Def x es   -> do
      reifyDisplayForm x es $ reifyDef expandAnonDefs x es
    I.Con c ci vs -> do
      let x = conName c
      isR <- isGeneratedRecordConstructor x
      case isR || ci == ConORec of
        True -> do
          showImp <- showImplicitArguments
          let keep (a, v) = showImp || visible a
          r  <- getConstructorData x
          xs <- getRecordFieldNames r
          vs <- map unArg <$> reify vs
          return $ A.Rec noExprInfo $ map (Left . uncurry FieldAssignment . mapFst unArg) $ filter keep $ zip xs vs
        False -> reifyDisplayForm x (map I.Apply vs) $ do
          def <- getConstInfo x
          let Constructor{conPars = np} = theDef def
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
              TelV tel _ <- telView (defType def)
              let (pars, rest) = splitAt np $ telToList tel
              case rest of
                -- Andreas, 2012-09-18
                -- If the first regular constructor argument is hidden,
                -- we keep the parameters to avoid confusion.
                (Dom {domInfo = info} : _) | notVisible info -> do
                  let us = for (drop n pars) $ \ (Dom {domInfo = ai}) ->
                             -- setRelevance Relevant $
                             hideOrKeepInstance $ Arg ai underscore
                  apps h $ us ++ es  -- Note: unless --show-implicit, @apps@ will drop @us@.
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
          | visible a   -> uncurry (A.Fun $ noExprInfo) <$> reify (a, b')
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
      ifM (asks envPrintMetasBare) {-then-} (return x') {-else-} $
        elims x' =<< reify es
    I.DontCare v -> A.DontCare <$> reifyTerm expandAnonDefs v
    I.Shared p   -> reifyTerm expandAnonDefs $ derefPtr p
  where
    -- Andreas, 2012-10-20  expand a copy if not in scope
    -- to improve error messages.
    -- Don't do this if we have just expanded into a display form,
    -- otherwise we loop!
    reifyDef :: Bool -> QName -> I.Elims -> TCM Expr
    reifyDef True x es =
      ifM (not . null . inverseScopeLookupName x <$> getScope) (reifyDef' x es) $ do
      r <- reduceDefCopy x es
      case r of
        YesReduction _ v -> do
          reportSLn "reify.anon" 60 $ unlines
            [ "reduction on defined ident. in anonymous module"
            , "x = " ++ prettyShow x
            , "v = " ++ show v
            ]
          reify v
        NoReduction () -> do
          reportSLn "reify.anon" 60 $ unlines
            [ "no reduction on defined ident. in anonymous module"
            , "x  = " ++ prettyShow x
            , "es = " ++ show es
            ]
          reifyDef' x es
    reifyDef _ x es = reifyDef' x es

    reifyDef' :: QName -> I.Elims -> TCM Expr
    reifyDef' x es = do
      reportSLn "reify.def" 60 $ "reifying call to " ++ prettyShow x
      -- We should drop this many arguments from the local context.
      n <- getDefFreeVars x
      reportSLn "reify.def" 70 $ "freeVars for " ++ prettyShow x ++ " = " ++ show n
      -- If the definition is not (yet) in the signature,
      -- we just do the obvious.
      let fallback = elims (A.Def x) =<< reify (drop n es)
      caseMaybeM (tryMaybe $ getConstInfo x) fallback $ \ defn -> do
      let def = theDef defn

      -- Check if we have an absurd lambda.
      case def of
       Function{ funCompiled = Just Fail, funClauses = [cl] }
                | isAbsurdLambdaName x -> do
                  -- get hiding info from last pattern, which should be ()
                  let h = getHiding $ last $ namedClausePats cl
                  elims (A.AbsurdLam noExprInfo h) =<< reify (drop n es)

      -- Otherwise (no absurd lambda):
       _ -> do

        -- Andrea(s), 2016-07-06
        -- Extended lambdas are not considered to be projection like,
        -- as they are mutually recursive with their parent.
        -- Thus we do not have to consider padding them.

        -- Check whether we have an extended lambda and display forms are on.
        df <- displayFormsEnabled
        toppars <- size <$> do lookupSection $ qnameModule x
        let extLam = case def of
             Function{ funExtLam = Just{}, funProjection = Just{} } -> __IMPOSSIBLE__
             Function{ funExtLam = Just (ExtLamInfo h nh) } -> Just (toppars + h + nh)
             _ -> Nothing
        case extLam of
          Just pars | df -> reifyExtLam x pars (defClauses defn) es

        -- Otherwise (ordinary function call):
          _ -> do
           (pad, nes :: [Elim' (Named_ Term)]) <- case def of

            Function{ funProjection = Just Projection{ projIndex = np } } | np > 0 -> do
              reportSLn "reify.def" 70 $ "  def. is a projection with projIndex = " ++ show np

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
              let pad = for as $ \ (Dom{domInfo = ai, unDom = (x, _)}) ->
                    Arg ai $ Named (Just $ unranged x) underscore

              -- Now pad' ++ es' = drop n (pad ++ es)
              let pad' = drop n pad
                  es'  = drop (max 0 (n - size pad)) es
              -- Andreas, 2012-04-21: get rid of hidden underscores {_} and {{_}}
              -- Keep non-hidden arguments of the padding.
              --
              -- Andreas, 2016-12-20, issue #2348:
              -- Let @padTail@ be the list of arguments of the padding
              -- (*) after the last visible argument of the padding, and
              -- (*) with the same visibility as the first regular argument.
              -- If @padTail@ is not empty, we need to
              -- print the first regular argument with name.
              -- We further have to print all elements of @padTail@
              -- which have the same name and visibility of the
              -- first regular argument.
              showImp <- showImplicitArguments

              -- Get the visible arguments of the padding and the rest
              -- after the last visible argument.
              let (padVisNamed, padRest) = filterAndRest visible pad'

              -- Remove the names from the visible arguments.
              let padVis  = map (fmap (unnamed . namedThing)) padVisNamed

              -- Keep only the rest with the same visibility of @dom@...
              let padTail = filter ((getHiding dom ==) . getHiding) padRest

              -- ... and even the same name.
              let padSame = filter ((Just (fst (unDom dom)) ==) . fmap rangedThing . nameOf . unArg) padTail

              return $ if null padTail || not showImp
                then (padVis           , map (fmap unnamed) es')
                else (padVis ++ padSame, nameFirstIfHidden dom es')

            -- If it is not a projection(-like) function, we need no padding.
            _ -> return ([], map (fmap unnamed) $ drop n es)

           reportSLn "reify.def" 70 $ unlines
             [ "  pad = " ++ show pad
             , "  nes = " ++ show nes
             ]
           let hd = foldl' (A.App noExprInfo) (A.Def x) pad
           nelims hd =<< reify nes

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

    reifyExtLam :: QName -> Int -> [I.Clause] -> I.Elims -> TCM Expr
    reifyExtLam x npars cls es = do
      reportSLn "reify.def" 10 $ "reifying extended lambda " ++ prettyShow x
      reportSLn "reify.def" 50 $ render $ nest 2 $ vcat
        [ text "npars =" <+> pretty npars
        , text "es    =" <+> fsep (map (prettyPrec 10) es)
        , text "def   =" <+> vcat (map pretty cls) ]
      -- As extended lambda clauses live in the top level, we add the whole
      -- section telescope to the number of parameters.
      let (pars, rest) = splitAt npars es
      -- Since we applying the clauses to the parameters,
      -- we do not need to drop their initial "parameter" patterns
      -- (this is taken care of by @apply@).
      cls <- mapM (reify . NamedClause x False . (`applyE` pars)) cls
      let cx    = nameConcrete $ qnameName x
          dInfo = mkDefInfo cx noFixity' PublicAccess ConcreteDef (getRange x)
      elims (A.ExtendedLam noExprInfo dInfo x cls) =<< reify rest

-- | @nameFirstIfHidden (x:a) ({e} es) = {x = e} es@
nameFirstIfHidden :: Dom (ArgName, t) -> [Elim' a] -> [Elim' (Named_ a)]
nameFirstIfHidden dom (I.Apply (Arg info e) : es) | notVisible info =
  I.Apply (Arg info (Named (Just $ unranged $ fst $ unDom dom) e)) :
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

-- instance Reify Elim Expr where
--   reifyWhen = reifyWhenE
--   reify e = case e of
--     I.IApply x y r -> appl "iapply" <$> reify (defaultArg r :: Arg Term)
--     I.Apply v -> appl "apply" <$> reify v
--     I.Proj f  -> appl "proj"  <$> reify ((defaultArg $ I.Def f []) :: Arg Term)
--     where
--       appl :: String -> Arg Expr -> Expr
--       appl s v = A.App exprInfo (A.Lit (LitString noRange s)) $ fmap unnamed v

data NamedClause = NamedClause QName Bool I.Clause
  -- ^ Also tracks whether module parameters should be dropped from the patterns.

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
          stripArgs fixedPos (a : as)
            -- Andreas, 2017-01-18, issue #819: preserves _ when splitting:
            -- An Inserted visible variable comes form a WildP and is restored as such.
            | visible a, getOrigin a == Inserted, varOrDot (namedArg a) = goWild
            -- A hidden non-UserWritten variable is removed if not needed for
            -- correct position of the following hidden arguments.
            | canStrip a =
                 if   all canStrip $ takeWhile isUnnamedHidden as
                 then stripArgs False as
                 else goWild
            -- Other arguments are kept.
            | otherwise = stripName fixedPos (stripArg a) : stripArgs True as
            where
              a'     = setNamedArg a $ A.WildP $ Info.PatRange $ getRange a
              goWild = stripName fixedPos a' : stripArgs True as

          stripName True  = fmap (unnamed . namedThing)
          stripName False = id

          canStrip a = and
            [ notVisible a
            , getOrigin a /= UserWritten
            , varOrDot (namedArg a)
            ]

          isUnnamedHidden x = notVisible x && nameOf (unArg x) == Nothing && isNothing (isProjP x)

          stripArg a = fmap (fmap stripPat) a

          stripPat p = case p of
            A.VarP _      -> p
            A.ConP i c ps -> A.ConP i c $ stripArgs True ps
            A.ProjP{}     -> p
            A.DefP _ _ _  -> p
            A.DotP _ _ e  -> p
            A.WildP _     -> p
            A.AbsurdP _   -> p
            A.LitP _      -> p
            A.AsP i x p   -> A.AsP i x $ stripPat p
            A.PatternSynP _ _ _ -> __IMPOSSIBLE__ -- p
            A.RecP i fs   -> A.RecP i $ map (fmap stripPat) fs  -- TODO Andreas: is this right?
            A.EqualP{}    -> p

          varOrDot A.VarP{}      = True
          varOrDot A.WildP{}     = True
          varOrDot A.DotP{}      = True
          varOrDot (A.ConP cpi _ ps) | patOrigin cpi == ConOSystem
                                 = all varOrDot $ map namedArg ps
          varOrDot _             = False

-- | @blank bound e@ replaces all variables in expression @e@ that are not in @bound@ by
--   an underscore @_@. It is used for printing dot patterns: we don't want to
--   make implicit variables explicit, so we blank them out in the dot patterns
--   instead (this is fine since dot patterns can be inferred anyway).

class BlankVars a where
  blank :: Set Name -> a -> a

  default blank :: (Functor f, BlankVars b, f b ~ a) => Set Name -> a -> a
  blank = fmap . blank

instance BlankVars a => BlankVars (Arg a)              where
instance BlankVars a => BlankVars (Named s a)          where
instance BlankVars a => BlankVars [a]                  where
-- instance BlankVars a => BlankVars (A.Pattern' a)       where  -- see case EqualP !
instance BlankVars a => BlankVars (FieldAssignment' a) where

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
    A.ProjP{}     -> p
    A.DefP i f ps -> A.DefP i f $ blank bound ps
    A.DotP i o e  -> A.DotP i o $ blank bound e
    A.WildP _     -> p
    A.AbsurdP _   -> p
    A.LitP _      -> p
    A.AsP i n p   -> A.AsP i n $ blank bound p
    A.PatternSynP _ _ _ -> __IMPOSSIBLE__
    A.RecP i fs   -> A.RecP i $ blank bound fs
    A.EqualP i es -> A.EqualP i (blank bound es)  -- Andrea TODO: is this correct?

instance BlankVars A.Expr where
  blank bound e = case e of
    A.ScopedExpr i e       -> A.ScopedExpr i $ blank bound e
    A.Var x                -> if x `Set.member` bound then e
                              else A.Underscore emptyMetaInfo  -- Here is the action!
    A.Def _                -> e
    A.Proj{}               -> e
    A.Con _                -> e
    A.Lit _                -> e
    A.QuestionMark{}       -> e
    A.Underscore _         -> e
    A.Dot i e              -> A.Dot i $ blank bound e
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

instance BlankVars A.ModuleName where
  blank bound = id

instance BlankVars RHS where
  blank bound (RHS e mc)             = RHS (blank bound e) mc
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


-- | Collect the binders in some abstract syntax lhs.

class Binder a where
  varsBoundIn :: a -> Set Name

  default varsBoundIn :: (Foldable f, Binder b, f b ~ a) => a -> Set Name
  varsBoundIn = foldMap varsBoundIn

instance Binder A.LHS where
  varsBoundIn (A.LHS _ core ps) = varsBoundIn (core, ps)

instance Binder A.LHSCore where
  varsBoundIn (A.LHSHead _ ps)   = varsBoundIn ps
  varsBoundIn (A.LHSProj _ b ps) = varsBoundIn (b, ps)

instance Binder A.Pattern where
  varsBoundIn = foldAPattern $ \case
    A.VarP x            -> if prettyShow x == "()" then empty else singleton x -- TODO: get rid of this hack?
    A.AsP _ x _         -> empty
    A.ConP _ _ _        -> empty
    A.ProjP{}           -> empty
    A.DefP _ _ _        -> empty
    A.WildP{}           -> empty
    A.DotP{}            -> empty
    A.AbsurdP{}         -> empty
    A.LitP{}            -> empty
    A.PatternSynP _ _ _ -> empty
    A.RecP _ _          -> empty
    A.EqualP{}          -> empty

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

instance Binder (WithHiding Name) where
  varsBoundIn (WithHiding _ x) = singleton x

instance Binder a => Binder (FieldAssignment' a) where
instance Binder a => Binder (Arg a)              where
instance Binder a => Binder (Named x a)          where
instance Binder a => Binder [a]                  where

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
      I.VarP x -> liftTCM $ A.VarP <$> nameOfBV (dbPatVarIndex x)
      I.DotP v -> do
        t <- liftTCM $ reify v
        -- This is only used for printing purposes, so the Origin shouldn't be
        -- used after this point anyway.
        return $ A.DotP patNoRange Inserted t
        -- WAS: return $ A.DotP patNoRange __IMPOSSIBLE__ t
        -- Crashes on -v 100.
      I.AbsurdP p -> return $ A.AbsurdP patNoRange
      I.LitP l  -> return $ A.LitP l
      I.ProjP o d     -> return $ A.ProjP patNoRange o $ AmbQ [d]
      I.ConP c cpi ps -> do
        liftTCM $ reportSLn "reify.pat" 60 $ "reifying pattern " ++ show p
        tryRecPFromConP =<< do A.ConP ci (AmbQ [conName c]) <$> reifyPatterns ps
        where
          ci = ConPatInfo origin patNoRange
          origin = fromMaybe ConOCon $ I.conPRecord cpi

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
          if recNamedCon def && patOrigin ci /= ConORec then fallback else do
            fs <- liftTCM $ getRecordFieldNames r
            unless (length fs == length ps) __IMPOSSIBLE__
            return $ A.RecP patNoRange $ zipWith mkFA fs ps
        where
          mkFA ax nap = FieldAssignment (unArg ax) (namedArg nap)
    _ -> __IMPOSSIBLE__

instance Reify (QNamed I.Clause) A.Clause where
  reify (QNamed f cl) = reify (NamedClause f True cl)

instance Reify NamedClause A.Clause where
  reify (NamedClause f toDrop cl) = addContext (clauseTel cl) $ do
    reportSLn "reify.clause" 60 $ "reifying NamedClause"
      ++ "\n  f      = " ++ prettyShow f
      ++ "\n  toDrop = " ++ show toDrop
      ++ "\n  cl     = " ++ show cl
    ps  <- reifyPatterns $ namedClausePats cl
    lhs <- liftTCM $ reifyDisplayFormP $ SpineLHS info f ps [] -- LHS info (LHSHead f ps) []
    -- Unless @toDrop@ we have already dropped the module patterns from the clauses
    -- (e.g. for extended lambdas).
    lhs <- if not toDrop then return lhs else do
      nfv <- getDefFreeVars f `catchError` \_ -> return 0
      return $ dropParams nfv lhs
    lhs <- stripImps lhs
    reportSLn "reify.clause" 60 $ "reifying NamedClause, lhs = " ++ show lhs
    rhs <- caseMaybe (clauseBody cl) (return AbsurdRHS) $ \ e -> do
       RHS <$> reify e <*> pure Nothing
    reportSLn "reify.clause" 60 $ "reifying NamedClause, rhs = " ++ show rhs
    let result = A.Clause (spineToLhs lhs) [] rhs [] (I.clauseCatchall cl)
    reportSLn "reify.clause" 60 $ "reified NamedClause, result = " ++ show result
    return result
    where
      perm = fromMaybe __IMPOSSIBLE__ $ clausePerm cl
      info = LHSRange noRange

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
    reify (Dom{domInfo = info, unDom = i}) = Arg info <$> reify i

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
