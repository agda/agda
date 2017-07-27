{-# LANGUAGE CPP #-}
-- | Sanity checking for internal syntax. Mostly checking variable scoping.
module Agda.Syntax.Internal.SanityCheck where

import Control.Monad
import qualified Data.IntSet as Set

import Text.PrettyPrint (empty)

import Agda.Syntax.Internal
import Agda.TypeChecking.Free
import Agda.TypeChecking.Monad
import Agda.TypeChecking.Substitute

import Agda.Utils.Pretty
import Agda.Utils.Size
import Agda.Utils.Impossible

#include "undefined.h"

sanityCheckVars :: (Pretty a, Free a) => Telescope -> a -> TCM ()
sanityCheckVars tel v =
  case filter bad (Set.toList $ allFreeVars v) of
    [] -> return ()
    xs -> do
      reportSDoc "impossible" 1 . return $
        sep [ hang (text "Sanity check failed for") 2
                   (hang (pretty tel <+> text "|-") 2 (pretty v))
            , text $ "out of scope: " ++ show xs ]
      __IMPOSSIBLE__
  where
    n     = size tel
    bad x = x < 0 || x >= n

-- | Check that @Γ ⊢ ρ : Δ@.
sanityCheckSubst :: (Pretty a, Free a) => Telescope -> Substitution' a -> Telescope -> TCM ()
sanityCheckSubst gamma rho delta = go gamma rho delta
  where
    go gamma rho delta =
      case rho of
        IdS      -> unless (size gamma == size delta) $ err $ text "idS:" <+> hang (pretty gamma <+> text "/=") 2 (pretty delta)
        EmptyS _ -> unless (size delta == 0) $ err $ text "emptyS:" <+> pretty delta <+> text "is not empty"
        v :# rho -> do
          unless (size delta > 0) $ err $ text "consS: empty target"
          sanityCheckVars gamma v
          sanityCheckSubst gamma rho (dropLast delta)
        Strengthen _ rho -> do
          unless (size delta > 0) $ err $ text "strS: empty target"
          sanityCheckSubst gamma rho (dropLast delta)
        Wk n rho -> do
          unless (size gamma >= n) $ err $ text "wkS:" <+> sep [ text "|" <> pretty gamma <> text "|"
                                                               , text $ "< " ++ show n ]
          sanityCheckSubst (dropLastN n gamma) rho delta
        Lift n rho -> do
          unless (size gamma >= n) $ err $ text "liftS: source" <+> sep [ text "|" <> pretty gamma <> text "|"
                                                                        , text $ "< " ++ show n ]
          unless (size delta >= n) $ err $ text "liftS: target" <+> sep [ text "|" <> pretty delta <> text "|"
                                                                        , text $ "< " ++ show n ]
          sanityCheckSubst (dropLastN n gamma) rho (dropLastN n delta)

    dropLast = telFromList . init . telToList
    dropLastN n = telFromList . reverse . drop n . reverse . telToList

    err reason = do
      reportSDoc "impossible" 1 . return $
        sep [ hang (text "Sanity check failed for") 2 $
              hang (pretty gamma <+> text "|-") 2 $
              hang (pretty rho <+> text ":") 2 $
                    pretty delta
            , reason ]
      __IMPOSSIBLE__

