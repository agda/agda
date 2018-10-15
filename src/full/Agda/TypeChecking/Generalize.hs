{-# LANGUAGE CPP #-}

module Agda.TypeChecking.Generalize (generalizeType) where

import Control.Arrow ((***))
import Control.Monad
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Map (Map)
import qualified Data.Map as Map
import Data.List (nub, partition)

import Agda.Syntax.Common
import Agda.Syntax.Position
import Agda.Syntax.Internal
import Agda.Syntax.Literal
import Agda.TypeChecking.Monad
import Agda.TypeChecking.Abstract
import Agda.TypeChecking.MetaVars
import Agda.TypeChecking.Pretty
import Agda.TypeChecking.Reduce
import Agda.TypeChecking.Substitute

import Agda.Utils.Functor
import Agda.Utils.Impossible
import Agda.Utils.Lens
import Agda.Utils.Maybe
import qualified Agda.Utils.Graph.TopSort as Graph

#include "undefined.h"

-- | Generalize a type over a set of (used) generalizable variables.
generalizeType :: Set QName -> TCM Type -> TCM (Int, Type)
generalizeType s m = do
    (t, allmetas) <- metasCreatedBy $ do
      -- Create metas for all used generalizable variables and their dependencies.
      cp      <- viewTC eCurrentCheckpoint
      genvals <- locallyTC eGeneralizeMetas (const YesGeneralize) $ forM (Set.toList s) $ \ x -> do
        def <- getConstInfo x
                         -- Only prefix of generalizable arguments (for now?)
        let nGen       = length $ takeWhile (== YesGeneralize) $ defArgGeneralizable def
            ty         = defType def
            TelV tel _ = telView' ty
            argTel     = telFromList $ take nGen $ telToList tel

        args <- newTelMeta argTel

        let metaType = piApply ty args
            name     = show (nameConcrete $ qnameName x)
        (m, term) <- newNamedValueMeta DontRunMetaOccursCheck name metaType

        -- Freeze the meta to prevent named generalizable metas to be instantiated.
        let fromJust' :: Lens' a (Maybe a)
            fromJust' f (Just x) = Just <$> f x
            fromJust' f Nothing  = {-'-} __IMPOSSIBLE__
        stMetaStore . key m . fromJust' . metaFrozen `setTCLens` Frozen

        -- Set up names of arg metas
        forM_ (zip3 [1..] (map unArg args) (telToList argTel)) $ \ case
          (i, MetaV m _, Dom{unDom = (x, _)}) -> do
            let suf "_" = show i
                suf ""  = show i
                suf x   = x
            setMetaNameSuggestion m (name ++ "." ++ suf x)
          _ -> return ()  -- eta expanded

        -- Update the ArgInfos for the named meta. The argument metas are
        -- created with the correct ArgInfo.
        setMetaArgInfo m $ defArgInfo def

        reportSDoc "tc.decl.gen" 50 $ vcat
          [ "created metas for generalized variable" <+> prettyTCM x
          , nest 2 $ "top  =" <+> prettyTCM term
          , nest 2 $ "args =" <+> prettyTCM args ]

        case term of
          MetaV{} -> return ()
          _       -> genericDocError =<< ("Cannot generalize over" <+> prettyTCM x <+> "of eta-expandable type") <?>
                                          prettyTCM metaType
        return (x, GeneralizedValue{ genvalCheckpoint = cp
                                   , genvalTerm       = term
                                   , genvalType       = metaType })

      -- Check the type
      let gvMap = Map.fromList genvals
      t <- locallyTC eGeneralizedVars (const gvMap) m

      return t

    -- Collect generalizable metas and sort them in dependency order.

    -- Pair metas with their metaInfo
    mvs <- mapM (\ x -> (x,) <$> lookupMeta x) (Set.toList allmetas)

    -- Split unsolved metas into generalizable and non-generalizable
    let isGeneralizable (_, mv) = YesGeneralize == unArg (miGeneralizable (mvInfo mv))
        openMetas = filter (isOpenMeta . mvInstantiation . snd) mvs
        (openGeneralizable, openNongeneralizable) = map fst *** map fst $ partition isGeneralizable openMetas

    -- For now, we don't handle unsolved non-generalizable metas.
    unless (null openNongeneralizable) $
      typeError $ NotImplemented "Unsolved non-generalizable metas in generalized type"

    metaGraph <- fmap concat $ forM openGeneralizable $ \ m -> do
                    deps <- nub . filter (`elem` openGeneralizable) . allMetas <$> (instantiateFull =<< getMetaType m)
                    return [ (m, m') | m' <- deps ]

    sortedMetas <- caseMaybe (Graph.topSort openGeneralizable metaGraph)
                             (typeError GeneralizeCyclicDependency)
                             return

    reportSDoc "tc.decl.gen" 50 $ vcat
      [ text $ "allMetas    = " ++ show allmetas
      , text $ "sortedMetas = " ++ show sortedMetas ]

    -- Generalize over metas
    t  <- instantiateFull t
    t' <- addVars t $ reverse sortedMetas
    reportSDoc "tc.decl.gen" 40 $ vcat
      [ "generalized"
      , nest 2 $ "t  =" <+> prettyTCM t
      , nest 2 $ "t' =" <+> prettyTCM t' ]

    -- Nuke the generalized metas
    forM_ sortedMetas $ \ m ->
      modifyMetaStore $ flip Map.adjust m $ \ mv ->
        -- TODO: check that they got generalized and then we can remove them completely
        mv { mvInstantiation = InstV [] $ Lit (LitString noRange ("meta var " ++ show m ++ " was generalized")) }
          -- (error ("meta var " ++ show m ++ " was generalized")) }

    return (length sortedMetas, t')
  where
    addVars t []       = return t
    addVars t (m : ms) = do
        mv <- lookupMeta m
        metaCp <- enterClosure (miClosRange $ mvInfo mv) $ \ _ -> viewTC eCurrentCheckpoint
        cp     <- viewTC eCurrentCheckpoint
        if | metaCp /= cp -> addVars t ms -- TODO: try to strengthen
           | otherwise    -> do
              vs <- getContextArgs
              ty <- (`piApply` vs) <$> getMetaType m
              let nas  = miNameSuggestion $ mvInfo mv
                  info = getArgInfo $ miGeneralizable $ mvInfo mv
              addTheVar info nas (MetaV m $ map Apply vs) ty t ms

    addTheVar info n v ty t ns = do
        ty <- instantiateFull ty
        t' <- mkPi (defaultArgDom info (n, ty)) <$> abstractType ty v t
        reportSDoc "tc.decl.gen" 60 $ vcat
            [ "generalize over"
            , nest 2 $ pretty v <+> ":" <+> pretty ty
            , nest 2 $ "in" <+> pretty t
            , nest 2 $ "to" <+> pretty t'
            ]
        addVars t' ns
