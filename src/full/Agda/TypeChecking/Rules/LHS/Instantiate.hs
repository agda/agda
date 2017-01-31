{-# LANGUAGE CPP #-}

module Agda.TypeChecking.Rules.LHS.Instantiate where

import Agda.Syntax.Common
import Agda.Syntax.Internal as I hiding (Substitution)
import qualified Agda.Syntax.Abstract as A
import Agda.Syntax.Abstract.Views ( asView )

import Agda.TypeChecking.Monad
import Agda.TypeChecking.Substitute hiding (Substitution)
import qualified Agda.TypeChecking.Substitute as S (Substitution)
import Agda.TypeChecking.Pretty
import Agda.TypeChecking.Reduce
import Agda.TypeChecking.Telescope

import Agda.TypeChecking.Rules.LHS.Problem

import Agda.Utils.List
import Agda.Utils.Permutation
import Agda.Utils.Size

#include "undefined.h"
import Agda.Utils.Impossible

-- | Instantiate a telescope with a substitution. Might reorder the telescope.
--   @instantiateTel (Γ : Tel)(σ : Γ --> Γ) = Γσ~@
--   Monadic only for debugging purposes.
instantiateTel :: Substitution -> Telescope -> TCM (Telescope, Permutation, S.Substitution, [Dom Type])
instantiateTel s tel = liftTCM $ do

  reportSDoc "tc.lhs.inst" 10 $ vcat
    [ text "instantiateTel "
    , nest 2 $ text "s    =" <+> do
        addContext tel $ fsep $ punctuate comma $ map (maybe (text "_") prettyTCM) s
    , nest 2 $ text "tel  =" <+> prettyTCM tel
--    , nest 2 $ text "tel  =" <+> text (show tel)
    ]

{-
  -- Andreas, 2013-10-27
  -- Why is normalization necessary?  Issue 234 seems to need it.
  -- But it is better done right before where it is needed (see below).

  tel <- normalise tel

  reportSDoc "tc.lhs.inst" 15 $ vcat
    [ nest 2 $ text "tel (normalized)=" <+> prettyTCM tel
    ]
-}

  -- Shrinking permutation (removing Justs) (and its complement, and reverse)
  let n   = size s
      {- OLD CODE, leave as documentation
      ps  = Perm n [ i | (i, Nothing) <- zip [0..] $ reverse s ]
      psR = reverseP ps
      psC = Perm n [ i | (i, Just _)  <- zip [0..] $ reverse s ]
      -}
      deal (i, Nothing) = Left i
      deal (i, Just _ ) = Right i
      (is, isC) = mapEither deal $ zip [0..] $ reverse s
      ps  = Perm n is
      psR = reverseP ps
      psC = Perm n isC

  reportSDoc "tc.lhs.inst" 10 $ vcat
    [ nest 2 $ text $ "ps   = " ++ show ps
    , nest 2 $ text $ "psR  = " ++ show psR
    , nest 2 $ text $ "psC  = " ++ show psC
    ]

  -- s' : Substitution Γσ
  let s' =  {-'-} renameP __IMPOSSIBLE__ psR s

  reportSDoc "tc.lhs.inst" 15 $ nest 2 $
    text "s'   =" <+> fsep (punctuate comma $ map (maybe (text "_") prettyTCM) s')

  -- rho : [Tm Γσ]Γ
  let rho = mkSubst s'

  reportSDoc "tc.lhs.inst" 15 $ nest 2 $
    text "rho = " <+> text (show rho)

  -- tel1 : [Type Γ]Γ
  let tel1   = flattenTel tel
      names1 = teleNames tel

  reportSDoc "tc.lhs.inst" 15 $ nest 2 $ vcat
    [ text "tel1 =" <+> brackets (fsep $ punctuate comma $ map prettyTCM tel1)
--    , text "tel1 =" <+> text (show tel1)
    ]

  -- tel2 : [Type Γσ]Γ
  let tel2 = applySubst rho tel1

  reportSDoc "tc.lhs.inst" 15 $ nest 2 $
    text "tel2 =" <+> brackets (fsep $ punctuate comma $ map prettyTCM tel2)

  -- tel3 : [Type Γσ]Γσ
  --
  -- Andreas, 2013-10-27
  -- @reorderTel@ below uses free variable analysis, so @tel3@ should be
  -- fully instantiated and normalized. (See issue 234.)
  -- Ulf, 2014-02-05: Only normalise if reordering fails!
  tel3 <- instantiateFull $ permute ps tel2
  let names3 = permute ps names1

  reportSDoc "tc.lhs.inst" 15 $ nest 2 $
    text "tel3 =" <+> brackets (fsep $ punctuate comma $ map prettyTCM tel3)

  -- Raise error if telescope cannot be ordered.
  let failToReorder = inTopContext $ addContext names3 $ do
        err <- sep [ text "Recursive telescope in left hand side:"
                   , fsep [ parens (text (argNameToString x) <+> text ":" <+> prettyTCM t)
                          | (x, t) <- zip names3 tel3 ]
                   ]
        typeError $ GenericError $ show err
      tryNormalisedReorder = do
        tel3 <- normalise tel3
        reportSDoc "tc.lhs.inst" 30 $ text "failed to reorder unnormalised, trying again with" $$
          nest 2 (text "norm =" <+> brackets (fsep $ punctuate comma $ map prettyTCM tel3))
        p <- maybe failToReorder return . reorderTel =<< normalise tel3
        return (p, tel3)

  -- p : Permutation (Γσ -> Γσ ~)
  (p, tel3) <- maybe tryNormalisedReorder (\p -> return (p, tel3)) $ reorderTel tel3

  reportSLn "tc.lhs.inst" 10 $ "  p   = " ++ show p

  -- rho' : [Term Γσ~]Γσ
  let rho' = {-'-} renaming __IMPOSSIBLE__ (reverseP p)

  -- tel4 : [Type Γσ~]Γσ~
  let tel4   = applySubst rho' (permute p tel3)
      names4 = permute p names3

  reportSDoc "tc.lhs.inst" 15 $ nest 2 $
    text "tel4 =" <+> brackets (fsep $ punctuate comma $ map prettyTCM tel4)

  -- tel5 = Γσ~
  let tel5 = unflattenTel names4 tel4

  reportSDoc "tc.lhs.inst" 15 $ nest 2 $
    text "tel5 =" <+> prettyTCM tel5

  -- remember the types of the instantiations
  -- itypes : [Type Γσ~]Γ*
  let itypes = applySubst rho' $ permute psC tel2

  return (tel5, composeP p ps, applySubst rho' rho, itypes)
  where

    -- Turn a Substitution ([Maybe Term]) into a substitution (S.Substitution)
    mkSubst :: [Maybe Term] -> S.Substitution
    mkSubst s = rho 0 s'
      where s'  = s
            rho i (Nothing : s) = consS (var i) $ rho (i + 1) s
            rho i (Just u  : s) = consS u $ rho i s
            rho i []            = raiseS i

-- | Produce a nice error message when splitting failed
nothingToSplitError :: Problem -> TCM a
nothingToSplitError (Problem ps _ tel pr) = splitError ps tel
  where
    splitError []       EmptyTel    = do
      if null $ restPats pr then __IMPOSSIBLE__ else do
        typeError $ GenericError $ "Arguments left we cannot split on. TODO: better error message"
    splitError (_:_)    EmptyTel    = __IMPOSSIBLE__
    splitError []       ExtendTel{} = __IMPOSSIBLE__
    splitError (p : ps) (ExtendTel a tel)
      | isBad p   = traceCall (CheckPattern (strip p) EmptyTel (unDom a)) $
                      typeError $ IlltypedPattern (strip p) (unDom a)
      | otherwise = underAbstraction a tel $ \tel -> splitError ps tel
      where
        strip = snd . asView . namedArg
        isBad p = case strip p of
          A.DotP{} -> True
          A.ConP{} -> True
          A.LitP{} -> True
          A.RecP{} -> True
          A.VarP{}    -> False
          A.WildP{}   -> False
          A.AbsurdP{} -> False
          A.EqualP{}      -> True -- __IMPOSSIBLE__ -- cubical constraints do not go through the splitter.
          A.ProjP{}        -> __IMPOSSIBLE__  -- Projection pattern gives CannotEliminateWithPattern
          A.DefP{}        -> __IMPOSSIBLE__
          A.AsP{}         -> __IMPOSSIBLE__
          A.PatternSynP{} -> __IMPOSSIBLE__
