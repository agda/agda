-- | Sanity checking for internal syntax. Mostly checking variable scoping.
module Agda.Syntax.Internal.SanityCheck where

import Control.Monad
import qualified Data.IntSet as Set

import Agda.Syntax.Internal
import Agda.TypeChecking.Free
import Agda.TypeChecking.Monad

import Agda.Utils.List ( dropEnd, initWithDefault )
import Agda.Utils.Pretty
import Agda.Utils.Size
import Agda.Utils.Impossible


sanityCheckVars :: (Pretty a, Free a) => Telescope -> a -> TCM ()
sanityCheckVars tel v =
  case filter bad (Set.toList $ allFreeVars v) of
    [] -> return ()
    xs -> do
      reportSDoc "impossible" 1 . return $
        sep [ hang "Sanity check failed for" 2
                   (hang (pretty tel <+> "|-") 2 (pretty v))
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
        IdS      -> unless (size gamma == size delta) $ err $ "idS:" <+> hang (pretty gamma <+> "/=") 2 (pretty delta)
        EmptyS _ -> unless (size delta == 0) $ err $ "emptyS:" <+> pretty delta <+> "is not empty"
        v :# rho -> do
          unless (size delta > 0) $ err $ "consS: empty target"
          sanityCheckVars gamma v
          sanityCheckSubst gamma rho (dropLast delta)
        Strengthen _ n rho -> do
          unless (size delta >= n) $ err $ "strS: empty target"
          sanityCheckSubst gamma rho (dropLastN n delta)
        Wk n rho -> do
          unless (size gamma >= n) $ err $ "wkS:" <+> sep [ "|" <> pretty gamma <> "|"
                                                               , text $ "< " ++ show n ]
          sanityCheckSubst (dropLastN n gamma) rho delta
        Lift n rho -> do
          unless (size gamma >= n) $ err $ "liftS: source" <+> sep [ "|" <> pretty gamma <> "|"
                                                                        , text $ "< " ++ show n ]
          unless (size delta >= n) $ err $ "liftS: target" <+> sep [ "|" <> pretty delta <> "|"
                                                                        , text $ "< " ++ show n ]
          sanityCheckSubst (dropLastN n gamma) rho (dropLastN n delta)

    dropLast = telFromList . initWithDefault __IMPOSSIBLE__ . telToList
    dropLastN n = telFromList . dropEnd n . telToList

    err reason = do
      reportSDoc "impossible" 1 . return $
        sep [ hang "Sanity check failed for" 2 $
              hang (pretty gamma <+> "|-") 2 $
              hang (pretty rho <+> ":") 2 $
                    pretty delta
            , reason ]
      __IMPOSSIBLE__
