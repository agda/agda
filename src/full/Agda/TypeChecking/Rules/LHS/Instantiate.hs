{-# LANGUAGE CPP #-}

module Agda.TypeChecking.Rules.LHS.Instantiate where

import Agda.Syntax.Common
import Agda.Syntax.Internal
import qualified Agda.Syntax.Abstract as A

import Agda.TypeChecking.Monad
import Agda.TypeChecking.Substitute hiding (Substitution)
import qualified Agda.TypeChecking.Substitute as S (Substitution)
import Agda.TypeChecking.Free
import Agda.TypeChecking.Pretty
import Agda.TypeChecking.Reduce
import Agda.TypeChecking.Telescope

import Agda.TypeChecking.Rules.LHS.Problem
-- import Agda.TypeChecking.Rules.LHS.ProblemRest
import Agda.TypeChecking.Rules.LHS.Split ( asView )

import Agda.Utils.List
import Agda.Utils.Permutation
import Agda.Utils.Size

#include "../../../undefined.h"
import Agda.Utils.Impossible

-- | Instantiate a telescope with a substitution. Might reorder the telescope.
--   @instantiateTel (Γ : Tel)(σ : Γ --> Γ) = Γσ~@
--   Monadic only for debugging purposes.
instantiateTel :: Substitution -> Telescope -> TCM (Telescope, Permutation, S.Substitution, [Dom Type])
instantiateTel s tel = liftTCM $ do

  tel <- normalise tel

  reportSDoc "tc.lhs.inst" 10 $ vcat
    [ text "instantiateTel "
    , nest 2 $ addCtxTel tel $ fsep $ punctuate comma $ map (maybe (text "_") prettyTCM) s
    , nest 2 $ text "tel  =" <+> prettyTCM tel
--    , nest 2 $ text "tel  =" <+> text (show tel)
    ]

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
  let s' = renameP psR s

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
  tel3 <- instantiateFull $ permute ps tel2
  let names3 = permute ps names1

  reportSDoc "tc.lhs.inst" 15 $ nest 2 $
    text "tel3 =" <+> brackets (fsep $ punctuate comma $ map prettyTCM tel3)

  -- p : Permutation (Γσ -> Γσ~)
  p <- case reorderTel tel3 of
    Nothing -> inContext [] $ do
      xs <- mapM freshName_ names3
      addCtxs xs (Dom NotHidden Relevant prop) $ do
        err <- sep [ text "Recursive telescope in left hand side:"
                   , fsep [ parens (prettyTCM x <+> text ":" <+> prettyTCM t)
                          | (x, t) <- zip xs tel3 ]
                   ]
        typeError $ GenericError $ show err
    Just p  -> return p

  reportSLn "tc.lhs.inst" 10 $ "p   = " ++ show p

  -- rho' : [Term Γσ~]Γσ
  let rho' = renaming (reverseP p)

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
	    rho i (Nothing : s) = var i :# rho (i + 1) s
	    rho i (Just u  : s) = u :# rho i s
	    rho i []		= raiseS i

-- | Produce a nice error message when splitting failed
nothingToSplitError :: Problem -> TCM a
nothingToSplitError (Problem ps _ tel pr) = splitError ps tel
  where
    splitError []	EmptyTel    = __IMPOSSIBLE__
    splitError (_:_)	EmptyTel    = __IMPOSSIBLE__
    splitError []	ExtendTel{} = __IMPOSSIBLE__
    splitError (p : ps) (ExtendTel a tel)
      | isBad p   = traceCall (CheckPattern (strip p) EmptyTel (unDom a)) $ case strip p of
	  A.DotP _ e -> typeError $ UninstantiatedDotPattern e
	  p	     -> typeError $ IlltypedPattern p (unDom a)
      | otherwise = underAbstraction a tel $ \tel -> splitError ps tel
      where
	strip = snd . asView . namedThing . unArg
	isBad p = case strip p of
	  A.DotP _ _   -> True
	  A.ConP _ _ _ -> True
	  A.LitP _     -> True
	  _	       -> False
