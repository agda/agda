{-# LANGUAGE CPP           #-}

module Agda.TypeChecking.Injectivity where

import Prelude hiding (mapM)

import Control.Applicative
import Control.Monad.State hiding (mapM, forM)
import Control.Monad.Reader hiding (mapM, forM)

import Data.Map (Map)
import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.Maybe
import Data.Traversable hiding (for)

import qualified Agda.Syntax.Abstract.Name as A
import Agda.Syntax.Common
import Agda.Syntax.Internal
import Agda.Syntax.Internal.Pattern

import Agda.TypeChecking.Monad
import Agda.TypeChecking.Substitute
import Agda.TypeChecking.Reduce
import Agda.TypeChecking.Primitive
import {-# SOURCE #-} Agda.TypeChecking.MetaVars
import {-# SOURCE #-} Agda.TypeChecking.Conversion
import Agda.TypeChecking.Pretty
import Agda.TypeChecking.Constraints
import Agda.TypeChecking.Polarity

import Agda.Utils.Except ( MonadError(catchError, throwError) )
import Agda.Utils.Functor
import Agda.Utils.List
import Agda.Utils.Maybe
import Agda.Utils.Permutation

#include "undefined.h"
import Agda.Utils.Impossible

headSymbol :: Term -> TCM (Maybe TermHead)
headSymbol v = do -- ignoreAbstractMode $ do
  -- Andreas, 2013-02-18 ignoreAbstractMode leads to information leakage

  v <- ignoreBlocking <$> reduceHead v
  case ignoreSharing v of
    Def f _ -> do
      let yes = return $ Just $ ConsHead f
          no  = return $ Nothing
      def <- theDef <$> do ignoreAbstractMode $ getConstInfo f
        -- Andreas, 2013-02-18
        -- if we do not ignoreAbstractMode here, abstract Functions get turned
        -- into Axioms, but we want to distinguish these.
      case def of
        Datatype{}  -> yes
        Record{}    -> yes
        Axiom{}     -> do
          reportSLn "tc.inj.axiom" 50 $ "headSymbol: " ++ show f ++ " is an Axiom."
          -- Don't treat axioms in the current mutual block
          -- as constructors (they might have definitions we
          -- don't know about yet).
          caseMaybeM (asks envMutualBlock) yes $ \ mb -> do
            fs <- mutualNames <$> lookupMutualBlock mb
            if Set.member f fs then no else yes
        Function{}    -> no
        Primitive{}   -> no
        Constructor{} -> __IMPOSSIBLE__
        AbstractDefn  -> __IMPOSSIBLE__
    Con c _ _ -> return (Just $ ConsHead $ conName c)
    Sort _  -> return (Just SortHead)
    Pi _ _  -> return (Just PiHead)
    Lit _   -> return Nothing -- handle literal heads as well? can't think of
                              -- any examples where it would be useful...
    Lam{}   -> return Nothing
    Var{}   -> return Nothing
    Level{} -> return Nothing
    MetaV{} -> return Nothing
    DontCare{} -> return Nothing
    Shared{}   -> __IMPOSSIBLE__

checkInjectivity :: QName -> [Clause] -> TCM FunctionInverse
checkInjectivity f cs
  | pointLess cs = do
      reportSLn "tc.inj.check.pointless" 20 $
        "Injectivity of " ++ show (A.qnameToConcrete f) ++ " would be pointless."
      return NotInjective
  where
    -- Is it pointless to use injectivity for this function?
    pointLess []      = True
    pointLess (_:_:_) = False
    pointLess [cl] = not $ any (properlyMatching . namedArg) $ namedClausePats cl
        -- Andreas, 2014-06-12
        -- If we only have record patterns, it is also pointless.
        -- We need at least one proper match.
checkInjectivity f cs = do
  reportSLn "tc.inj.check" 40 $ "Checking injectivity of " ++ show f
  -- Extract the head symbol of the rhs of each clause (skip absurd clauses)
  es <- catMaybes <$> do
    forM cs $ \ c -> do             -- produces a list ...
      mapM ((,c) <.> headSymbol) $ clauseBody c -- ... of maybes
  let (hs, ps) = unzip es
  reportSLn "tc.inj.check" 40 $ "  right hand sides: " ++ show hs
  if all isJust hs && distinct hs
    then do
      let inv = Map.fromList (map fromJust hs `zip` ps)
      reportSLn "tc.inj.check" 20 $ show f ++ " is injective."
      reportSDoc "tc.inj.check" 30 $ nest 2 $ vcat $
        for (Map.toList inv) $ \ (h, c) ->
          text (show h) <+> text "-->" <+>
          fsep (punctuate comma $ map (prettyTCM . namedArg) $ namedClausePats c)
      return $ Inverse inv
    else return NotInjective

-- | Argument should be in weak head normal form.
functionInverse :: Term -> TCM InvView
functionInverse v = case ignoreSharing v of
  Def f es -> do
    d <- theDef <$> getConstInfo f
    case d of
      Function{ funInv = inv } -> case inv of
        NotInjective  -> return NoInv
        Inverse m     -> return $ Inv f es m
          -- NB: Invertible functions are never classified as
          --     projection-like, so this is fine, we are not
          --     missing parameters.  (Andreas, 2013-11-01)
      _ -> return NoInv
  _ -> return NoInv

data InvView = Inv QName [Elim] (Map TermHead Clause)
             | NoInv

data MaybeAbort = Abort | KeepGoing

useInjectivity :: Comparison -> Type -> Term -> Term -> TCM ()
useInjectivity cmp a u v = do
  reportSDoc "tc.inj.use" 30 $ fsep $
    pwords "useInjectivity on" ++
    [ prettyTCM u, prettyTCM cmp, prettyTCM v, text ":", prettyTCM a
    ]
  uinv <- functionInverse u
  vinv <- functionInverse v
  case (uinv, vinv) of
    -- Andreas, Francesco, 2014-06-12:
    -- We know that one of u,v is neutral
    -- (see calls to useInjectivity in Conversion.hs).
    -- Otherwise, (e.g. if both were Blocked), the following case would be
    -- unsound, since it assumes the arguments to be pointwise equal.
    -- It would deliver non-unique solutions for metas.
    (Inv f fArgs _, Inv g gArgs _)
      | f == g    -> do
        a <- defType <$> getConstInfo f
        reportSDoc "tc.inj.use" 20 $ vcat
          [ fsep (pwords "comparing application of injective function" ++ [prettyTCM f] ++
                pwords "at")
          , nest 2 $ fsep $ punctuate comma $ map prettyTCM fArgs
          , nest 2 $ fsep $ punctuate comma $ map prettyTCM gArgs
          , nest 2 $ text "and type" <+> prettyTCM a
          ]
        pol <- getPolarity' cmp f
        compareElims pol a (Def f []) fArgs gArgs
      | otherwise -> fallBack
    (Inv f args inv, NoInv) -> do
      a <- defType <$> getConstInfo f
      reportSDoc "tc.inj.use" 20 $ fsep $
        pwords "inverting injective function" ++
        [ prettyTCM f, text ":", prettyTCM a, text "for", prettyTCM v
        , parens $ text "args =" <+> prettyList (map prettyTCM args)
        ]
      invert u f a inv args =<< headSymbol v
    (NoInv, Inv g args inv) -> do
      a <- defType <$> getConstInfo g
      reportSDoc "tc.inj.use" 20 $ fsep $
        pwords "inverting injective function" ++
        [ prettyTCM g, text ":", prettyTCM a,  text "for", prettyTCM u
        , parens $ text "args =" <+> prettyList (map prettyTCM args)
        ]
      invert v g a inv args =<< headSymbol u
    (NoInv, NoInv)          -> fallBack
  where
    fallBack = addConstraint $ ValueCmp cmp a u v

    invert :: Term -> QName -> Type -> Map TermHead Clause -> [Elim] -> Maybe TermHead -> TCM ()
    invert _ _ a inv args Nothing  = fallBack
    invert org f ftype inv args (Just h) = case Map.lookup h inv of
      Nothing -> typeError $ UnequalTerms cmp u v a
      Just cl@Clause{ clauseTel  = tel } -> maybeAbort $ do
          let ps   = clausePats cl
              perm = fromMaybe __IMPOSSIBLE__ $ clausePerm cl
          -- These are what dot patterns should be instantiated at
          ms <- map unArg <$> newTelMeta tel
          reportSDoc "tc.inj.invert" 20 $ vcat
            [ text "meta patterns" <+> prettyList (map prettyTCM ms)
            , text "  perm =" <+> text (show perm)
            , text "  tel  =" <+> prettyTCM tel
            , text "  ps   =" <+> prettyList (map (text . show) ps)
            ]
          -- and this is the order the variables occur in the patterns
          let msAux = permute (invertP __IMPOSSIBLE__ $ compactP perm) ms
          let sub   = parallelS (reverse ms)
          margs <- runReaderT (evalStateT (mapM metaElim ps) msAux) sub
          reportSDoc "tc.inj.invert" 20 $ vcat
            [ text "inversion"
            , nest 2 $ vcat
              [ text "lhs  =" <+> prettyTCM margs
              , text "rhs  =" <+> prettyTCM args
              , text "type =" <+> prettyTCM ftype
              ]
            ]
          -- Since we do not care for the value of non-variant metas here,
          -- we can treat 'Nonvariant' as 'Invariant'.
          -- That ensures these metas do not remain unsolved.
          pol <- purgeNonvariant <$> getPolarity' cmp f
          -- The clause might not give as many patterns as there
          -- are arguments (point-free style definitions).
          let args' = take (length margs) args
          compareElims pol ftype (Def f []) margs args'
{- Andreas, 2011-05-09 allow unsolved constraints as long as progress
          unless (null cs) $ do
            reportSDoc "tc.inj.invert" 30 $
              text "aborting inversion; remaining constraints" <+> prettyTCM cs
            patternViolation
-}
          -- Check that we made progress, i.e. the head symbol
          -- of the original term should be a constructor.
          org <- reduce org
          h <- headSymbol org
          case h of
            Just h  -> KeepGoing <$ compareTerm cmp a u v
            Nothing -> do
              reportSDoc "tc.inj.invert" 30 $ vcat
                [ text "aborting inversion;" <+> prettyTCM org
                , text "plainly," <+> text (show org)
                , text "has TermHead" <+> text (show h)
                , text "which does not expose a constructor"
                ]
              return Abort

    maybeAbort m = do
      (a, s) <- localTCStateSaving m
      case a of
        KeepGoing -> put s
        Abort     -> fallBack

    nextMeta = do
      m : ms <- get
      put ms
      return m

    dotP :: Monad m => Term -> StateT [Term] (ReaderT Substitution m) Term
    dotP v = do
      sub <- ask
      return $ applySubst sub v

    metaElim (Arg _ (ProjP o p))  = lift $ lift $ Proj o <$> getOriginalProjection p
    metaElim (Arg info p)         = Apply . Arg info <$> metaPat p

    metaArgs args = mapM (traverse $ metaPat . namedThing) args

    metaPat (DotP v)         = dotP v
    metaPat (VarP _)         = nextMeta
    metaPat (AbsurdP p)      = metaPat p
    metaPat (ConP c mt args) = Con c (fromConPatternInfo mt) <$> metaArgs args
    metaPat (LitP l)         = return $ Lit l
    metaPat ProjP{}          = __IMPOSSIBLE__
