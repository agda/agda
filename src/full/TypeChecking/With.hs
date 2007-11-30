{-# OPTIONS -cpp #-}
module TypeChecking.With where

import Control.Applicative
import Control.Monad
import Control.Monad.State
import qualified Data.Traversable as T (mapM)
import Data.List

import Syntax.Common
import Syntax.Internal
import Syntax.Abstract (LHS(..), RHS(..))
import qualified Syntax.Abstract as A

import TypeChecking.Monad
import TypeChecking.Substitute
import TypeChecking.Reduce
import TypeChecking.Primitive hiding (Nat)
import TypeChecking.Pretty
import TypeChecking.Rules.LHS.Implicit
import TypeChecking.Abstract

import Utils.Permutation
import Utils.Size

#include "../undefined.h"

showPat (VarP x)    = text x
showPat (DotP t)    = comma <> text (showsPrec 10 t "")
showPat (ConP c ps) = parens $ prettyTCM c <+> fsep (map (showPat . unArg) ps)
showPat (LitP l)    = text (show l)

withFunctionType :: Telescope -> [Term] -> [Type] -> Telescope -> Type -> TCM Type
withFunctionType delta1 vs as delta2 b = do
  vas <- normalise $ zip vs as
  b   <- normalise $ telePi delta2 b
  return $ telePi delta1 $ foldr (uncurry piAbstractTerm) b vas

-- | Compute the clauses for the with-function given the original patterns.
buildWithFunction :: QName -> Telescope -> [Arg Pattern] -> Permutation ->
                     Nat -> Nat -> [A.Clause] -> TCM [A.Clause]
buildWithFunction aux gamma qs perm n1 n cs = mapM buildWithClause cs
  where
    buildWithClause (A.Clause (LHS i _ ps wps) rhs wh) = do
      let (wps0, wps1) = splitAt n wps
          ps0          = map (Arg NotHidden . unnamed) wps0
      rhs <- buildRHS rhs
      (ps1, ps2)  <- splitAt n1 <$> stripWithClausePatterns gamma qs perm ps
      return $ A.Clause (LHS i aux (ps1 ++ ps0 ++ ps2) wps1) rhs wh

    buildRHS rhs@(RHS _)     = return rhs
    buildRHS rhs@AbsurdRHS   = return rhs
    buildRHS (WithRHS es cs) = WithRHS es <$> mapM buildWithClause cs

{-| @stripWithClausePatterns Γ qs π ps = ps'@

    @Δ@ - context bound by lhs of original function (not an argument)

    @Γ@ - type of arguments to original function

    @qs@ - internal patterns for original function

    @π@ - permutation taking @vars(qs)@ to @support(Δ)@

    @ps@ - patterns in with clause (presumably of type @Γ@)

    @ps'@ - patterns for with function (presumably of type @Δ@)
-}
stripWithClausePatterns :: Telescope -> [Arg Pattern] -> Permutation -> [NamedArg A.Pattern] -> TCM [NamedArg A.Pattern]
stripWithClausePatterns gamma qs perm ps = do
  psi <- insertImplicitPatterns ps gamma
  unless (size psi == size gamma) $ fail $ "wrong number of arguments in with clause: given " ++ show (size psi) ++ ", expected " ++ show (size gamma)
  ps' <- strip gamma psi qs
  -- TODO: remember dot patterns
  reportSDoc "tc.with.strip" 10 $ vcat
    [ text "stripping patterns"
    , nest 2 $ text "gamma = " <+> prettyTCM gamma
    , nest 2 $ text "psi = " <+> fsep (punctuate comma $ map prettyA psi)
    , nest 2 $ text "ps' = " <+> fsep (punctuate comma $ map prettyA ps')
    , nest 2 $ text "psp = " <+> fsep (punctuate comma $ map prettyA $ permute perm ps')
    , nest 2 $ text "qs  = " <+> fsep (punctuate comma $ map (showPat . unArg) qs)
    ]

  return $ permute perm ps'
  where
    -- implicit args inserted at top level
    -- all three arguments should have the same size
    strip :: Telescope -> [NamedArg A.Pattern] -> [Arg Pattern] -> TCM [NamedArg A.Pattern]
    strip _           []      (_ : _) = __IMPOSSIBLE__    -- This case doesn't trigger!!
    strip _           (_ : _) []      = __IMPOSSIBLE__
    strip EmptyTel    (_ : _) _       = __IMPOSSIBLE__
    strip ExtendTel{} []      _       = __IMPOSSIBLE__
    strip EmptyTel    []      []      | 0 == 0 = return []
    strip (ExtendTel a tel) (p : ps) (q : qs) = do
      reportSDoc "tc.with.strip" 15 $ vcat
        [ text "strip" 
        , nest 2 $ text "ps =" <+> fsep (punctuate comma $ map prettyA (p : ps))
        , nest 2 $ text "qs =" <+> fsep (punctuate comma $ map (showPat . unArg) (q : qs))
        , nest 2 $ text "tel=" <+> prettyTCM (ExtendTel a tel)
        ]
      case unArg q of
        VarP _  -> do
          ps <- underAbstraction a tel $ \tel -> strip tel ps qs
          return $ p : ps

        DotP _  -> do
          ps <- underAbstraction a tel $ \tel -> strip tel ps qs
          return $ p : ps

        ConP c qs' -> case namedThing $ unArg p of
          A.ConP _ c' ps' -> do
          
            Con c  [] <- constructorForm =<< reduce (Con c [])
            Con c' [] <- constructorForm =<< reduce (Con c' [])

            unless (c == c') mismatch

            -- The type is a datatype
            Def d us <- normalise $ unEl (unArg a)

            -- Compute the argument telescope for the constructor
            Con c []    <- constructorForm =<< normalise (Con c [])
            Defn _ ct _ _ (Constructor np _ _ _)  <- getConstInfo c
            reportSDoc "tc.with.strip" 20 $ text "ct = " <+> prettyTCM ct
            let ct' = flip apply (take np us) ct
            reportSDoc "tc.with.strip" 20 $ text "ct' = " <+> prettyTCM ct
            reportSDoc "tc.with.strip" 20 $ text "us = " <+> prettyList (map prettyTCM $ take np us)

            TelV tel' _ <- telView . flip apply (take np us) . defType <$> getConstInfo c

            -- Compute the new telescope
            let v     = Con c $ reverse [ Arg h (Var i []) | (i, Arg h _) <- zip [0..] $ reverse qs' ]
                tel'' = tel' `abstract` absApp (raise (size tel') tel) v

            reportSDoc "tc.with.strip" 15 $ sep
              [ text "inserting implicit"
              , nest 2 $ prettyList $ map prettyA (ps' ++ ps)
              , nest 2 $ text ":" <+> prettyTCM tel''
              ]

            -- Insert implicit patterns (just for error message)
            psi' <- insertImplicitPatterns ps' tel'
            unless (size psi' == size tel') $ typeError $ WrongNumberOfConstructorArguments c (size tel') (size psi')

            -- Do it again for everything
            psi' <- insertImplicitPatterns (ps' ++ ps) tel''

            -- Keep going
            strip tel'' psi' (qs' ++ qs)
          _ -> mismatch

        LitP lit -> case namedThing $ unArg p of
          A.LitP lit' | lit == lit' -> strip (tel `absApp` Lit lit) ps qs
          _ -> mismatch
      where
        mismatch = typeError $ WithClausePatternMismatch (namedThing $ unArg p) (unArg q)
    strip tel ps qs = error $ "huh? " ++ show (size tel) ++ " " ++ show (size ps) ++ " " ++ show (size qs)

-- | Construct the display form for a with function. It will display
--   applications of the with function as applications to the original function.
--   For instance, @aux a b c@ as @f (suc a) (suc b) | c@
withDisplayForm :: QName -> QName -> Telescope -> Telescope -> Nat -> [Arg Pattern] -> Permutation -> TCM DisplayForm
withDisplayForm f aux delta1 delta2 n qs perm = do
  topArgs <- raise (n + size delta1 + size delta2) <$> getContextArgs
  x <- freshNoName_
  let wild = Def (qualify (mnameFromList []) x) []

  let top = length topArgs
      vs = topArgs ++ raiseFrom (size delta2) n (substs (sub wild) $ patsToTerms qs)
      dt = DWithApp (map DTerm $ Def f vs : withArgs) []
      withArgs = map var [size delta2..size delta2 + n - 1]
      pats = replicate (n + size delta1 + size delta2 + top) (Var 0 [])

  reportSDoc "tc.with.display" 20 $ vcat
    [ text "withDisplayForm"
    , nest 2 $ vcat
      [ text "delta1 =" <+> prettyTCM delta1
      , text "delta2 = " <+> prettyTCM delta2
      , text "perm   =" <+> text (show perm)
      , text "dt     =" <+> prettyTCM dt
      ]
    ]

  return $ Display (n + size delta1 + size delta2 + top) pats dt
  where
    var i = Var i []
    sub wild = map term [0..] -- m - 1]
      where
        Perm m xs = reverseP perm
        term i = case findIndex (i ==) xs of
          Nothing -> wild
          Just j  -> Var j []

patsToTerms :: [Arg Pattern] -> [Arg Term]
patsToTerms ps = evalState (toTerms ps) 0
  where
    mapMr f xs = reverse <$> mapM f (reverse xs)

    var :: State Nat Nat
    var = do
      i <- get
      put (i + 1)
      return i

    toTerms :: [Arg Pattern] -> State Nat [Arg Term]
    toTerms ps = mapMr toArg ps

    toArg :: Arg Pattern -> State Nat (Arg Term)
    toArg = T.mapM toTerm

    toTerm :: Pattern -> State Nat Term
    toTerm p = case p of
      VarP _    -> var >>= \i -> return $ Var i []
      DotP t    -> return t
      ConP c ps -> Con c <$> toTerms ps
      LitP l    -> return $ Lit l

