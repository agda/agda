{-# LANGUAGE CPP #-}

module Agda.TypeChecking.Rules.LHS where

import Data.Maybe
import qualified Data.List as List

import Control.Applicative
import Control.Monad

import Agda.Syntax.Internal as I
import Agda.Syntax.Internal.Pattern
import qualified Agda.Syntax.Abstract as A
import Agda.Syntax.Common
import Agda.Syntax.Info
import Agda.Syntax.Position

import Agda.TypeChecking.Monad
import Agda.TypeChecking.Pretty
import Agda.TypeChecking.Records -- isRecord
import Agda.TypeChecking.Reduce
import Agda.TypeChecking.Substitute hiding (Substitution)
import qualified Agda.TypeChecking.Substitute as S (Substitution)
import Agda.TypeChecking.Telescope
import Agda.TypeChecking.Conversion
import Agda.TypeChecking.Constraints
import Agda.TypeChecking.Irrelevance
import Agda.TypeChecking.Primitive (constructorForm)
import {-# SOURCE #-} Agda.TypeChecking.Empty
-- Duplicate import??
-- import Agda.TypeChecking.Telescope (renamingR, teleArgs)

import {-# SOURCE #-} Agda.TypeChecking.Rules.Term (checkExpr)
import Agda.TypeChecking.Rules.LHS.Problem
import Agda.TypeChecking.Rules.LHS.ProblemRest
import Agda.TypeChecking.Rules.LHS.Unify
import Agda.TypeChecking.Rules.LHS.Split
import Agda.TypeChecking.Rules.LHS.Implicit
import Agda.TypeChecking.Rules.LHS.Instantiate
import Agda.TypeChecking.Rules.Data

import Agda.Interaction.Highlighting.Generate

import Agda.Utils.Permutation
import Agda.Utils.Size
import Agda.Utils.Monad

#include "../../undefined.h"
import Agda.Utils.Impossible

-- | Compute the set of flexible patterns in a list of patterns. The result is
--   the deBruijn indices of the flexible patterns. A pattern is flexible if it
--   is dotted or implicit.
flexiblePatterns :: [A.NamedArg A.Pattern] -> TCM FlexibleVars
flexiblePatterns nps = map setArg <$> filterM (flexible . namedArg . snd) (zip [0..] $ reverse nps)
  where
    setArg (i, Arg ai _) = Arg ai i
    flexible (A.DotP _ _)    = return True
    flexible (A.ImplicitP _) = return True
    flexible (A.ConP _ (A.AmbQ [c]) qs) =
      ifM (isJust <$> isRecordConstructor c)
          (andM $ map (flexible . namedArg) qs)
          (return False)
    flexible _               = return False

-- | Compute the dot pattern instantiations.
dotPatternInsts :: [A.NamedArg A.Pattern] -> Substitution -> [I.Dom Type] -> TCM [DotPatternInst]
dotPatternInsts ps s as = dpi (map namedArg ps) (reverse s) as
  where
    dpi (_ : _)  []            _       = __IMPOSSIBLE__
    dpi (_ : _)  (Just _ : _)  []      = __IMPOSSIBLE__
    -- the substitution also contains entries for module parameters, so it can
    -- be longer than the pattern
    dpi []       _             _       = return []
    dpi (_ : ps) (Nothing : s) as      = dpi ps s as
    dpi (p : ps) (Just u : s) (a : as) =
      case p of
        A.DotP _ e    -> (DPI e u a :) <$> dpi ps s as
        A.ImplicitP _ -> dpi ps s as
        -- record pattern
        A.ConP _ (A.AmbQ [c]) qs -> do
          Def r vs   <- ignoreSharing <$> reduce (unEl $ unDom a)
          (ftel, us) <- etaExpandRecord r vs u
          qs <- insertImplicitPatterns ExpandLast qs ftel
          let instTel EmptyTel _                   = []
              instTel (ExtendTel arg tel) (u : us) = arg : instTel (absApp tel u) us
              instTel ExtendTel{} []               = __IMPOSSIBLE__
              bs0 = instTel ftel (map unArg us)
              -- Andreas, 2012-09-19 propagate relevance info to dot patterns
              bs  = map (mapRelevance (composeRelevance (getRelevance a))) bs0
          dpi (map namedArg qs ++ ps) (map (Just . unArg) us ++ s) (bs ++ as)

        _           -> __IMPOSSIBLE__

instantiatePattern :: Substitution -> Permutation -> [I.Arg Pattern] -> [I.Arg Pattern]
instantiatePattern sub perm ps
  | length sub /= length hps = error $ unlines [ "instantiatePattern:"
                                               , "  sub  = " ++ show sub
                                               , "  perm = " ++ show perm
                                               , "  ps   = " ++ show ps
                                               ]
  | otherwise  = foldr merge ps $ zipWith inst (reverse sub) hps
  where
    hps = permute perm $ allHoles ps
    inst Nothing  hps = Nothing
    inst (Just t) hps = Just $ plugHole (DotP t) hps

    merge Nothing   ps = ps
    merge (Just qs) ps = zipWith mergeA qs ps
      where
        mergeA a1 a2 = a1 { unArg = mergeP (unArg a1) (unArg a2) }
        mergeP (DotP s)  (DotP t)
          | s == t                    = DotP s
          | otherwise                 = __IMPOSSIBLE__
        mergeP (DotP t)  (VarP _)     = DotP t
        mergeP (VarP _)  (DotP t)     = DotP t
        mergeP (DotP _)  _            = __IMPOSSIBLE__
        mergeP _         (DotP _)     = __IMPOSSIBLE__
        mergeP (ConP c1 mt1 ps) (ConP c2 mt2 qs)
          | c1 == c2                  = ConP (c1 `withRangeOf` c2) (mplus mt1 mt2) $ zipWith mergeA ps qs
          | otherwise                 = __IMPOSSIBLE__
        mergeP (LitP l1) (LitP l2)
          | l1 == l2                  = LitP (l1 `withRangeOf` l2)
          | otherwise                 = __IMPOSSIBLE__
        mergeP (VarP x) (VarP y)
          | x == y                    = VarP x
          | otherwise                 = __IMPOSSIBLE__
        mergeP (ConP _ _ _) (VarP _)  = __IMPOSSIBLE__
        mergeP (ConP _ _ _) (LitP _)  = __IMPOSSIBLE__
        mergeP (VarP _) (ConP _ _ _)  = __IMPOSSIBLE__
        mergeP (VarP _) (LitP _)      = __IMPOSSIBLE__
        mergeP (LitP _) (ConP _ _ _)  = __IMPOSSIBLE__
        mergeP (LitP _) (VarP _)      = __IMPOSSIBLE__

-- | Check if a problem is solved. That is, if the patterns are all variables.
isSolvedProblem :: Problem -> Bool
isSolvedProblem = all (isVar . snd . asView . namedArg) . problemInPat
  where
    isVar (A.VarP _)      = True
    isVar (A.WildP _)     = True
    isVar (A.ImplicitP _) = True
    isVar (A.AbsurdP _)   = True
    isVar _               = False

-- | For each user-defined pattern variable in the 'Problem', check
-- that the corresponding data type (if any) does not contain a
-- constructor of the same name (which is not in scope); this
-- \"shadowing\" could indicate an error, and is not allowed.
--
-- Precondition: The problem has to be solved.

{-
noShadowingOfConstructors
  :: A.Clause
     -- ^ The entire clause (used for error reporting).
  -> Problem -> TCM ()
noShadowingOfConstructors c problem =
  traceCall (CheckPatternShadowing c) $ do
-}
noShadowingOfConstructors
  :: (Maybe r -> Call) -- ^ Trace, e.g., @CheckPatternShadowing clause@
  -> Problem -> TCM ()
noShadowingOfConstructors mkCall problem =
  traceCall mkCall $ do
    let pat = map (snd . asView . namedArg) $
                  problemInPat problem
        tel = map (unEl . snd . unDom) $ telToList $ problemTel problem
    zipWithM' noShadowing pat tel
    return ()
  where
  noShadowing (A.WildP     {}) t = return ()
  noShadowing (A.AbsurdP   {}) t = return ()
  noShadowing (A.ImplicitP {}) t = return ()
  noShadowing (A.ConP      {}) t = return ()  -- only happens for eta expanded record patterns
  noShadowing (A.DefP      {}) t = __IMPOSSIBLE__
  noShadowing (A.AsP       {}) t = __IMPOSSIBLE__
  noShadowing (A.DotP      {}) t = __IMPOSSIBLE__
  noShadowing (A.LitP      {}) t = __IMPOSSIBLE__
  noShadowing (A.PatternSynP {}) t = __IMPOSSIBLE__
  noShadowing (A.VarP x)       t = do
    t <- normalise t
    case t of
      Def t _ -> do
        d <- theDef <$> getConstInfo t
        case d of
          Datatype { dataCons = cs } -> do
            let ns = map (\c -> (c, A.nameConcrete $ A.qnameName c)) cs
                match x = catMaybes $
                            map (\(c, n) -> if A.nameConcrete x == n
                                            then Just c else Nothing) ns
            case match x of
              []      -> return ()
              (c : _) -> setCurrentRange (getRange x) $
                typeError $ PatternShadowsConstructor x c
          Axiom       {} -> return ()
          Function    {} -> return ()
          Record      {} -> return ()
          Constructor {} -> __IMPOSSIBLE__
          Primitive   {} -> __IMPOSSIBLE__
      Var   {} -> return ()
      Pi    {} -> return ()
      Sort  {} -> return ()
      Shared p -> noShadowing (A.VarP x) $ derefPtr p
      MetaV {} -> return ()
      -- TODO: If the type is a meta-variable, should the test be
      -- postponed? If there is a problem, then it will be caught when
      -- the completed module is type checked, so it is safe to skip
      -- the test here. However, users may be annoyed if they get an
      -- error in code which has already passed the type checker.
      Lam   {} -> __IMPOSSIBLE__
      Lit   {} -> __IMPOSSIBLE__
      Level {} -> __IMPOSSIBLE__
      Con   {} -> __IMPOSSIBLE__
      DontCare{} -> __IMPOSSIBLE__

-- | Check that a dot pattern matches it's instantiation.
checkDotPattern :: DotPatternInst -> TCM ()
checkDotPattern (DPI e v (Dom info a)) =
  traceCall (CheckDotPattern e v) $ do
  reportSDoc "tc.lhs.dot" 15 $
    sep [ text "checking dot pattern"
        , nest 2 $ prettyA e
        , nest 2 $ text "=" <+> prettyTCM v
        , nest 2 $ text ":" <+> prettyTCM a
        ]
  applyRelevanceToContext (argInfoRelevance info) $ do
    u <- checkExpr e a
    -- Should be ok to do noConstraints here
    noConstraints $ equalTerm a u v

-- | Bind the variables in a left hand side. Precondition: the patterns should
--   all be 'A.VarP', 'A.WildP', or 'A.ImplicitP' and the telescope should have
--   the same size as the pattern list.
--   There could also be 'A.ConP's resulting from eta expanded implicit record
--   patterns.
bindLHSVars :: [A.NamedArg A.Pattern] -> Telescope -> TCM a -> TCM a
bindLHSVars []       (ExtendTel _ _)   _   = __IMPOSSIBLE__
bindLHSVars (_ : _)   EmptyTel         _   = __IMPOSSIBLE__
bindLHSVars []        EmptyTel         ret = ret
bindLHSVars (p : ps) (ExtendTel a tel) ret =
  case namedArg p of
    A.VarP x      -> addCtx x a $ bindLHSVars ps (absBody tel) ret
    A.WildP _     -> bindDummy (absName tel)
    A.ImplicitP _ -> bindDummy (absName tel)
    A.AbsurdP pi  -> do
      -- Andreas, 2012-03-15: allow postponement of emptyness check
      isEmptyType (getRange pi) $ unDom a
      -- OLD CODE: isReallyEmptyType $ unArg a
      bindDummy (absName tel)
    A.ConP _ (A.AmbQ [c]) qs -> do -- eta expanded record pattern
      Def r vs <- reduce (unEl $ unDom a)
      ftel     <- (`apply` vs) <$> getRecordFieldTypes r
      let n   = size ftel
          eta = Con c [ Var i [] <$ (namedThing <$> setArgColors [] q) | (q, i) <- zip qs [n - 1, n - 2..0] ]
          -- ^ TODO guilhem
      bindLHSVars (qs ++ ps) (ftel `abstract` absApp (raise (size ftel) tel) eta) ret
    A.ConP{}        -> __IMPOSSIBLE__
    A.DefP{}        -> __IMPOSSIBLE__
    A.AsP{}         -> __IMPOSSIBLE__
    A.DotP{}        -> __IMPOSSIBLE__
    A.LitP{}        -> __IMPOSSIBLE__
    A.PatternSynP{} -> __IMPOSSIBLE__
    where
      name "_" = freshNoName_
      name s   = freshName_ ("." ++ s)
      bindDummy s = do
        x <- name s
        addCtx x a $ bindLHSVars ps (absBody tel) ret

-- | Bind as patterns
bindAsPatterns :: [AsBinding] -> TCM a -> TCM a
bindAsPatterns []                ret = ret
bindAsPatterns (AsB x v a : asb) ret = do
  reportSDoc "tc.lhs.as" 10 $ text "as pattern" <+> prettyTCM x <+>
    sep [ text ":" <+> prettyTCM a
        , text "=" <+> prettyTCM v
        ]
  addLetBinding defaultArgInfo x v a $ bindAsPatterns asb ret

-- | Check a LHS. Main function.
checkLeftHandSide
  :: (Maybe r -> Call)
     -- ^ Trace, e.g. @CheckPatternShadowing clause@
  -> [A.NamedArg A.Pattern]
     -- ^ The patterns.
  -> Type
     -- ^ The expected type @a = Γ → b@.
  -> (Maybe Telescope   -- Γ : The types of the patterns.
                        -- 'Nothing' if more patterns than domain types in @a@.
                        -- Used only to construct a @with@ function; see 'stripwithClausePatterns'.
      -> Telescope      -- Δ : The types of the pattern variables.
      -> S.Substitution -- σ : The patterns in form of a substitution Δ ⊢ σ : Γ
      -> [String]       -- Names for the variables in Δ, for binding the body.
      -> [I.Arg Pattern]-- The patterns in internal syntax.
      -> Type           -- The type of the body. Is @bσ@ if @Γ@ is defined.
      -> Permutation    -- The permutation from pattern vars to @Δ@.
      -> TCM a)
     -- ^ Continuation.
  -> TCM a
checkLeftHandSide c ps a ret = do
  problem <- problemFromPats ps a
  unless (noProblemRest problem) $ typeError $ TooManyArgumentsInLHS a
  let (Problem _ _ gamma (ProblemRest _ b)) = problem
      mgamma = if noProblemRest problem then Just gamma else Nothing
      st     = LHSState problem idS [] []

  -- doing the splits:
  LHSState (Problem ps (perm, qs) delta rest) sigma dpi asb <- checkLHS st
  unless (null $ restPats rest) $ typeError $ TooManyArgumentsInLHS a

  -- let b' = applySubst sigma b
  let b' = restType rest

  noPatternMatchingOnCodata qs

  reportSDoc "tc.lhs.top" 10 $
    vcat [ text "checked lhs:"
	 , nest 2 $ vcat
	   [ text "ps    = " <+> fsep (map prettyA ps)
	   , text "perm  = " <+> text (show perm)
	   , text "delta = " <+> prettyTCM delta
	   , text "dpi   = " <+> brackets (fsep $ punctuate comma $ map prettyTCM dpi)
	   , text "asb   = " <+> brackets (fsep $ punctuate comma $ map prettyTCM asb)
           , text "qs    = " <+> text (show qs)
	   ]
         ]
  bindLHSVars ps delta $ bindAsPatterns asb $ do
    reportSDoc "tc.lhs.top" 10 $ nest 2 $ text "type  = " <+> prettyTCM b'

    -- Check dot patterns
    mapM_ checkDotPattern dpi

    let rho = renamingR perm -- I'm not certain about this...
        Perm n _ = perm
        xs  = [ "h" ++ show n | n <- [0..n - 1] ]
    ret mgamma delta rho xs qs b' perm
  where
    -- the loop: split at a variable in the problem until problem is solved
    checkLHS :: LHSState -> TCM LHSState
    checkLHS st@(LHSState problem sigma dpi asb) = do
      problem <- insertImplicitProblem problem  -- inserting implicits no longer preserve solvedness
      if isSolvedProblem problem                -- since we might insert eta expanded record patterns
        then do
          noShadowingOfConstructors c problem
          return $ st { lhsProblem = problem }
        else do
        sp <- splitProblem problem
        reportSDoc "tc.lhs.split" 20 $ text "splitting completed"
        case sp of
          Left NothingToSplit   -> nothingToSplitError problem
          Left (SplitPanic err) -> __IMPOSSIBLE__

          -- Split on literal pattern
          Right (Split p0 xs (Arg _ (LitFocus lit iph hix a)) p1) -> do

            -- plug the hole with a lit pattern
            let ip    = plugHole (LitP lit) iph
                iperm = expandP hix 0 $ fst (problemOutPat problem)

            -- substitute the literal in p1 and sigma and dpi and asb
            let delta1 = problemTel p0
                delta2 = absApp (fmap problemTel p1) (Lit lit)
                rho    = liftS (size delta2) $ singletonS (Lit lit)
                -- rho    = [ var i | i <- [0..size delta2 - 1] ]
                --       ++ [ raise (size delta2) $ Lit lit ]
                --       ++ [ var i | i <- [size delta2 ..] ]
                sigma'   = applySubst rho sigma
                dpi'     = applySubst rho dpi
                asb0     = applySubst rho asb
                ip'      = applySubst rho ip
                rest'    = applySubst rho (problemRest problem)

            -- Compute the new problem
            let ps'      = problemInPat p0 ++ problemInPat (absBody p1)
                delta'   = abstract delta1 delta2
                problem' = Problem ps' (iperm, ip') delta' rest'
                asb'     = raise (size delta2) (map (\x -> AsB x (Lit lit) a) xs) ++ asb0
            st' <- updateProblemRest (LHSState problem' sigma' dpi' asb')
            checkLHS st'

          -- Split on constructor pattern
          Right (Split p0 xs (Arg info
                  ( Focus { focusCon      = c
                          , focusConArgs  = qs
                          , focusRange    = r
                          , focusOutPat   = iph
                          , focusHoleIx   = hix
                          , focusDatatype = d
                          , focusParams   = vs
                          , focusIndices  = ws
                          , focusType     = a
                          }
                  )) p1
                ) -> traceCall (CheckPattern (A.ConP (PatRange r) (A.AmbQ [c]) qs)
                                             (problemTel p0)
                                             (El Prop $ Def d $ vs ++ ws)) $ do

            let delta1 = problemTel p0
            let typeOfSplitVar = Arg info a

            reportSDoc "tc.lhs.split" 10 $ sep
              [ text "checking lhs"
              , nest 2 $ text "tel =" <+> prettyTCM (problemTel problem)
              , nest 2 $ text "rel =" <+> (text $ show $ argInfoRelevance info)
              ]

            reportSDoc "tc.lhs.split" 15 $ sep
              [ text "split problem"
              , nest 2 $ vcat
                [ text "delta1 = " <+> prettyTCM delta1
                , text "typeOfSplitVar =" <+> prettyTCM typeOfSplitVar
                , text "focusOutPat =" <+> (text . show) iph
                , text "delta2 = " <+> prettyTCM (problemTel $ absBody p1)
                ]
              ]

            Con c' [] <- ignoreSharing <$> (constructorForm =<< normalise (Con c []))
            c  <- return $ c' `withRangeOf` c
            ca <- defType <$> getConstInfo c

            reportSDoc "tc.lhs.split" 20 $ nest 2 $ vcat
              [ text "ca =" <+> prettyTCM ca
              , text "vs =" <+> prettyList (map prettyTCM vs)
              ]

            -- Lookup the type of the constructor at the given parameters
            let a = ca `piApply` vs

            -- It will end in an application of the datatype
            (gamma', ca, d', us) <- do
              TelV gamma' ca@(El _ def) <- telView a
              let Def d' us = ignoreSharing def
              return (gamma', ca, d', us)

            -- This should be the same datatype as we split on
            unless (d == d') $ typeError $ ShouldBeApplicationOf ca d'

{-
            reportSDoc "tc.lhs.top" 20 $ nest 2 $ vcat
              [ text "gamma' =" <+> text (show gamma')
              ]
-}

            -- Andreas 2010-09-07  propagate relevance info to new vars
            gamma' <- return $ fmap (applyRelevance $ argInfoRelevance info) gamma'
{-
            reportSDoc "tc.lhs.top" 20 $ nest 2 $ vcat
              [ text "gamma' =" <+> text (show gamma')
              ]
-}
            -- Insert implicit patterns
            qs' <- insertImplicitPatterns ExpandLast qs gamma'

            unless (size qs' == size gamma') $
              typeError $ WrongNumberOfConstructorArguments c (size gamma') (size qs')

            let gamma = useNamesFromPattern qs' gamma'

            -- Get the type of the datatype.
            da <- (`piApply` vs) . defType <$> getConstInfo d

            -- Compute the flexible variables
            flex <- flexiblePatterns (problemInPat p0 ++ qs')

	    reportSDoc "tc.lhs.top" 15 $ addCtxTel delta1 $
	      sep [ text "preparing to unify"
		  , nest 2 $ vcat
		    [ text "c      =" <+> prettyTCM c <+> text ":" <+> prettyTCM a
		    , text "d      =" <+> prettyTCM d <+> text ":" <+> prettyTCM da
		    , text "gamma  =" <+> prettyTCM gamma
		    , text "gamma' =" <+> prettyTCM gamma'
		    , text "vs     =" <+> brackets (fsep $ punctuate comma $ map prettyTCM vs)
		    , text "ws     =" <+> brackets (fsep $ punctuate comma $ map prettyTCM ws)
		    ]
		  ]

            -- Unify constructor target and given type (in Δ₁Γ)
            sub0 <- addCtxTel (delta1 `abstract` gamma) $
                    unifyIndices_ flex (raise (size gamma) da) (drop (size vs) us) (raise (size gamma) ws)

            -- We should substitute c ys for x in Δ₂ and sigma
            let ys     = teleArgs gamma
                delta2 = absApp (raise (size gamma) $ fmap problemTel p1) (Con c ys)
                rho0   = liftS (size delta2) $ Con c ys :# raiseS (size gamma)
                -- rho0 = [ var i | i <- [0..size delta2 - 1] ]
                --     ++ [ raise (size delta2) $ Con c ys ]
                --     ++ [ var i | i <- [size delta2 + size gamma ..] ]
                sigma0 = applySubst rho0 sigma
                dpi0   = applySubst rho0 dpi
                asb0   = applySubst rho0 asb
                rest0  = applySubst rho0 (problemRest problem)

            reportSDoc "tc.lhs.top" 15 $ addCtxTel (delta1 `abstract` gamma) $ nest 2 $ vcat
              [ text "delta2 =" <+> prettyTCM delta2
              , text "sub0   =" <+> brackets (fsep $ punctuate comma $ map (maybe (text "_") prettyTCM) sub0)
              ]
            reportSDoc "tc.lhs.top" 15 $ addCtxTel (delta1 `abstract` gamma `abstract` delta2) $
              nest 2 $ vcat
                [ text "dpi0 = " <+> brackets (fsep $ punctuate comma $ map prettyTCM dpi0)
                , text "asb0 = " <+> brackets (fsep $ punctuate comma $ map prettyTCM asb0)
                ]

            -- Andreas, 2010-09-09, save the type a of record pattern.
            -- It is relative to delta1, but it should be relative to
            -- all variables which will be bound by patterns.
            -- Thus, it has to be raised by 1 (the "hole" variable)
            -- plus the length of delta2 (the variables coming after the hole).
            storedPatternType <- ifM (isJust <$> isRecord d)
              (return $ Just $ raise (1 + size delta2) $ typeOfSplitVar)
              (return $ Nothing)

            -- Plug the hole in the out pattern with c ys
            let ysp = map (argFromDom . fmap (VarP . fst)) $ telToList gamma
                ip  = plugHole (ConP c storedPatternType ysp) iph
                ip0 = applySubst rho0 ip

            -- Δ₁Γ ⊢ sub0, we need something in Δ₁ΓΔ₂
            -- Also needs to be padded with Nothing's to have the right length.
            let pad n xs x = xs ++ replicate (max 0 $ n - size xs) x
                newTel = problemTel p0 `abstract` (gamma `abstract` delta2)
                sub    = replicate (size delta2) Nothing ++
                         pad (size delta1 + size gamma) (raise (size delta2) sub0) Nothing

            reportSDoc "tc.lhs.top" 15 $ nest 2 $ vcat
              [ text "newTel =" <+> prettyTCM newTel
              , addCtxTel newTel $ text "sub =" <+> brackets (fsep $ punctuate comma $ map (maybe (text "_") prettyTCM) sub)
              , text "ip   =" <+> text (show ip)
              , text "ip0  =" <+> text (show ip0)
              ]
            reportSDoc "tc.lhs.top" 15 $ nest 2 $ vcat
              [ text "rho0 =" <+> text (show rho0)
              ]

            -- Instantiate the new telescope with the given substitution
            (delta', perm, rho, instTypes) <- instantiateTel sub newTel


            reportSDoc "tc.lhs.inst" 12 $
              vcat [ sep [ text "instantiateTel"
                         , nest 4 $ brackets $ fsep $ punctuate comma $ map (maybe (text "_") prettyTCM) sub
                         , nest 4 $ prettyTCM newTel
                         ]
                   , nest 2 $ text "delta' =" <+> prettyTCM delta'
                   , nest 2 $ text "perm   =" <+> text (show perm)
                   , nest 2 $ text "itypes =" <+> fsep (punctuate comma $ map prettyTCM instTypes)
                   ]

{-          -- Andreas, 2010-09-09
            -- temporary error message to find non-id perms
            let sorted (Perm _ xs) = xs == List.sort xs
            unless (sorted (perm)) $ typeError $ GenericError $ "detected proper permutation " ++ show perm
-}
            -- Compute the new dot pattern instantiations
            let ps0'   = problemInPat p0 ++ qs' ++ problemInPat (absBody p1)

            reportSDoc "tc.lhs.top" 15 $ nest 2 $ vcat
              [ text "subst rho sub =" <+> brackets (fsep $ punctuate comma $ map (maybe (text "_") prettyTCM) (applySubst rho sub))
              , text "ps0'  =" <+> brackets (fsep $ punctuate comma $ map prettyA ps0')
              ]

            newDpi <- dotPatternInsts ps0' (applySubst rho sub) instTypes

            -- The final dpis and asbs are the new ones plus the old ones substituted by ρ
            let dpi' = applySubst rho dpi0 ++ newDpi
                asb' = applySubst rho $ asb0 ++ raise (size delta2) (map (\x -> AsB x (Con c ys) ca) xs)

            reportSDoc "tc.lhs.top" 15 $ nest 2 $ vcat
              [ text "dpi' = " <+> brackets (fsep $ punctuate comma $ map prettyTCM dpi')
              , text "asb' = " <+> brackets (fsep $ punctuate comma $ map prettyTCM asb')
              ]

            -- Apply the substitution to the type
            let sigma'   = applySubst rho sigma0
                rest'    = applySubst rho rest0

            reportSDoc "tc.lhs.inst" 15 $
              nest 2 $ text "ps0 = " <+> brackets (fsep $ punctuate comma $ map prettyA ps0')

            -- Permute the in patterns
            let ps'  = permute perm ps0'

           -- Compute the new permutation of the out patterns. This is the composition of
            -- the new permutation with the expansion of the old permutation to
            -- reflect the split.
            let perm'  = expandP hix (size gamma) $ fst (problemOutPat problem)
                iperm' = perm `composeP` perm'

            -- Instantiate the out patterns
            let ip'    = instantiatePattern sub perm' ip0
                newip  = applySubst rho ip'

            -- Construct the new problem
            let problem' = Problem ps' (iperm', newip) delta' rest'

            reportSDoc "tc.lhs.top" 12 $ sep
              [ text "new problem"
              , nest 2 $ vcat
                [ text "ps'    = " <+> fsep (map prettyA ps')
                , text "delta' = " <+> prettyTCM delta'
                ]
              ]

            reportSDoc "tc.lhs.top" 14 $ nest 2 $ vcat
              [ text "perm'  =" <+> text (show perm')
              , text "iperm' =" <+> text (show iperm')
              ]
            reportSDoc "tc.lhs.top" 14 $ nest 2 $ vcat
              [ text "ip'    =" <+> text (show ip')
              , text "newip  =" <+> text (show newip)
              ]

            -- if rest type reduces,
            -- extend the split problem by previously not considered patterns
            st'@(LHSState problem'@(Problem ps' (iperm', ip') delta' rest')
                          sigma' dpi' asb')
              <- updateProblemRest $ LHSState problem' sigma' dpi' asb'

            reportSDoc "tc.lhs.top" 12 $ sep
              [ text "new problem from rest"
              , nest 2 $ vcat
                [ text "ps'    = " <+> fsep (map prettyA ps')
                , text "delta' = " <+> prettyTCM delta'
                , text "ip'    =" <+> text (show ip')
                , text "iperm' =" <+> text (show iperm')
                ]
              ]
            -- Continue splitting
            checkLHS st'

-- Ensures that we are not performing pattern matching on codata.

noPatternMatchingOnCodata :: [I.Arg Pattern] -> TCM ()
noPatternMatchingOnCodata = mapM_ (check . unArg)
  where
  check (VarP {})   = return ()
  check (DotP {})   = return ()
  check (LitP {})   = return ()  -- Literals are assumed not to be coinductive.
  check (ConP q _ ps) = do
    TelV _ t <- telView' . defType <$> getConstInfo q
    c <- isCoinductive t
    case c of
      Nothing    -> __IMPOSSIBLE__
      Just False -> mapM_ (check . unArg) ps
      Just True  -> typeError $
        GenericError "Pattern matching on codata is not allowed"
