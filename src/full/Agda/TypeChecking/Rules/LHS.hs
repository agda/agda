{-# LANGUAGE CPP #-}

module Agda.TypeChecking.Rules.LHS where

import Data.Maybe
import Control.Applicative
import Control.Monad

import Agda.Syntax.Internal
import Agda.Syntax.Internal.Pattern
import qualified Agda.Syntax.Abstract as A
import Agda.Syntax.Common
import Agda.Syntax.Info
import Agda.Syntax.Position

import Agda.TypeChecking.Monad
import Agda.TypeChecking.Pretty
import Agda.TypeChecking.Reduce
import Agda.TypeChecking.Substitute
import Agda.TypeChecking.Conversion
import Agda.TypeChecking.Constraints
import Agda.TypeChecking.Primitive (constructorForm)
import {-# SOURCE #-} Agda.TypeChecking.Empty (isEmptyType)
import Agda.TypeChecking.Telescope (renamingR, teleArgs)

import Agda.TypeChecking.Rules.Term (checkExpr)
import Agda.TypeChecking.Rules.LHS.Problem
import Agda.TypeChecking.Rules.LHS.Unify
import Agda.TypeChecking.Rules.LHS.Split
import Agda.TypeChecking.Rules.LHS.Implicit
import Agda.TypeChecking.Rules.LHS.Instantiate
import Agda.TypeChecking.Rules.Data

import Agda.Utils.Permutation
import Agda.Utils.Size
import Agda.Utils.Monad

#include "../../undefined.h"
import Agda.Utils.Impossible

data DotPatternInst = DPI A.Expr Term Type
data AsBinding      = AsB Name Term Type

instance Subst DotPatternInst where
  substs us      (DPI e v a) = uncurry (DPI e) $ substs us (v,a)
  substUnder n u (DPI e v a) = uncurry (DPI e) $ substUnder n u (v,a)

instance PrettyTCM DotPatternInst where
  prettyTCM (DPI e v a) = sep [ prettyA e <+> text "="
                              , nest 2 $ prettyTCM v <+> text ":"
                              , nest 2 $ prettyTCM a
                              ]

instance Subst AsBinding where
  substs us      (AsB x v a) = uncurry (AsB x) $ substs us (v, a)
  substUnder n u (AsB x v a) = uncurry (AsB x) $ substUnder n u (v, a)

instance Raise AsBinding where
  raiseFrom m k (AsB x v a) = uncurry (AsB x) $ raiseFrom m k (v, a)

instance PrettyTCM AsBinding where
  prettyTCM (AsB x v a) =
    sep [ prettyTCM x <> text "@" <> parens (prettyTCM v)
        , nest 2 $ text ":" <+> prettyTCM a
        ]

-- | Compute the set of flexible patterns in a list of patterns. The result is
--   the deBruijn indices of the flexible patterns. A pattern is flexible if it
--   is dotted or implicit.
flexiblePatterns :: [NamedArg A.Pattern] -> FlexibleVars
flexiblePatterns nps = [ i | (i, p) <- zip [0..] $ reverse ps, flexible p ]
  where
    ps = map (namedThing . unArg) nps
    flexible (A.DotP _ _)    = True
    flexible (A.ImplicitP _) = True
    flexible _               = False

-- | Compute the dot pattern instantiations.
dotPatternInsts :: [NamedArg A.Pattern] -> Substitution -> [Type] -> [DotPatternInst]
dotPatternInsts ps s as = dpi (map (namedThing . unArg) ps) (reverse s) as
  where
    dpi (_ : _)  []            _       = __IMPOSSIBLE__
    dpi (_ : _)  (Just _ : _)  []      = __IMPOSSIBLE__
    -- the substitution also contains entries for module parameters, so it can
    -- be longer than the pattern
    dpi []       _             _       = []
    dpi (_ : ps) (Nothing : s) as      = dpi ps s as
    dpi (p : ps) (Just u : s) (a : as) = 
      case p of
        A.DotP _ e    -> DPI e u a : dpi ps s as
        A.ImplicitP _ -> dpi ps s as
        _           -> __IMPOSSIBLE__

instantiatePattern :: Substitution -> Permutation -> [Arg Pattern] -> [Arg Pattern]
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
        mergeA (Arg h p) (Arg _ q) = Arg h $ mergeP p q
        mergeP (DotP s)  (DotP t)
          | s == t                 = DotP s
          | otherwise              = __IMPOSSIBLE__
        mergeP (DotP t)  (VarP _)  = DotP t
        mergeP (VarP _)  (DotP t)  = DotP t
        mergeP (DotP _)  _         = __IMPOSSIBLE__
        mergeP _         (DotP _)  = __IMPOSSIBLE__
        mergeP (ConP c1 ps) (ConP c2 qs)
          | c1 == c2               = ConP (c1 `withRangeOf` c2) $ zipWith mergeA ps qs
          | otherwise              = __IMPOSSIBLE__
        mergeP (LitP l1) (LitP l2)
          | l1 == l2               = LitP (l1 `withRangeOf` l2)
          | otherwise              = __IMPOSSIBLE__
        mergeP (VarP x) (VarP y)
          | x == y                 = VarP x
          | otherwise              = __IMPOSSIBLE__
        mergeP (ConP _ _) (VarP _) = __IMPOSSIBLE__
        mergeP (ConP _ _) (LitP _) = __IMPOSSIBLE__
        mergeP (VarP _) (ConP _ _) = __IMPOSSIBLE__
        mergeP (VarP _) (LitP _)   = __IMPOSSIBLE__
        mergeP (LitP _) (ConP _ _) = __IMPOSSIBLE__
        mergeP (LitP _) (VarP _)   = __IMPOSSIBLE__

-- | Check if a problem is solved. That is, if the patterns are all variables.
isSolvedProblem :: Problem -> Bool
isSolvedProblem = all (isVar . snd . asView . namedThing . unArg) . problemInPat
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

noShadowingOfConstructors
  :: A.Clause
     -- ^ The entire clause (used for error reporting).
  -> Problem -> TCM ()
noShadowingOfConstructors c problem =
  traceCall (CheckPatternShadowing c) $ do
    let pat = map (snd . asView . namedThing . unArg) $
                  problemInPat problem
        tel = map (unEl . snd . unArg) $ telToList $ problemTel problem
    zipWithM' noShadowing pat tel
    return ()
  where
  noShadowing (A.WildP     {}) t = return ()
  noShadowing (A.AbsurdP   {}) t = return ()
  noShadowing (A.ImplicitP {}) t = return ()
  noShadowing (A.ConP      {}) t = __IMPOSSIBLE__
  noShadowing (A.DefP      {}) t = __IMPOSSIBLE__
  noShadowing (A.AsP       {}) t = __IMPOSSIBLE__
  noShadowing (A.DotP      {}) t = __IMPOSSIBLE__
  noShadowing (A.LitP      {}) t = __IMPOSSIBLE__
  noShadowing (A.VarP x)       t = do
    t <- normalise t
    case t of
      Def t _ -> do
        d <- theDef <$> getConstInfo (force t)
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
      Fun   {} -> return ()
      Sort  {} -> return ()
      MetaV {} -> return ()
      -- TODO: If the type is a meta-variable, should the test be
      -- postponed? If there is a problem, then it will be caught when
      -- the completed module is type checked, so it is safe to skip
      -- the test here. However, users may be annoyed if they get an
      -- error in code which has already passed the type checker.
      Lam   {} -> __IMPOSSIBLE__
      Lit   {} -> __IMPOSSIBLE__
      Con   {} -> __IMPOSSIBLE__

-- | Check that a dot pattern matches it's instantiation.
checkDotPattern :: DotPatternInst -> TCM ()
checkDotPattern (DPI e v a) =
  traceCall (CheckDotPattern e v) $ do
  reportSDoc "tc.lhs.dot" 15 $
    sep [ text "checking dot pattern"
        , nest 2 $ prettyA e
        , nest 2 $ text "=" <+> prettyTCM v
        , nest 2 $ text ":" <+> prettyTCM a
        ]
  u <- checkExpr e a
  noConstraints $ equalTerm a u v

-- | Bind the variables in a left hand side. Precondition: the patterns should
--   all be 'A.VarP', 'A.WildP', or 'A.ImplicitP' and the telescope should have
--   the same size as the pattern list.
bindLHSVars :: [NamedArg A.Pattern] -> Telescope -> TCM a -> TCM a
bindLHSVars []       (ExtendTel _ _)   _   = __IMPOSSIBLE__
bindLHSVars (_ : _)   EmptyTel         _   = __IMPOSSIBLE__
bindLHSVars []        EmptyTel         ret = ret
bindLHSVars (p : ps) (ExtendTel a tel) ret =
  case namedThing $ unArg p of
    A.VarP x      -> addCtx x a $ bindLHSVars ps (absBody tel) ret
    A.WildP _     -> bindDummy (absName tel)
    A.ImplicitP _ -> bindDummy (absName tel)
    A.AbsurdP _   -> do
      isEmptyType $ unArg a
      bindDummy (absName tel)
    _             -> __IMPOSSIBLE__
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
  addLetBinding x v a $ bindAsPatterns asb ret

-- | Rename the variables in a telescope using the names from a given pattern
useNamesFromPattern :: [NamedArg A.Pattern] -> Telescope -> Telescope
useNamesFromPattern ps = telFromList . zipWith ren (toPats ps ++ repeat dummy) . telToList
  where
    dummy = A.WildP __IMPOSSIBLE__
    ren (A.VarP x) (Arg NotHidden (_, a)) = Arg NotHidden (show x, a)
    ren _ a = a
    toPats = map (namedThing . unArg)

-- | Check a LHS. Main function.
checkLeftHandSide
  :: A.Clause
     -- ^ The entire clause.
  -> [NamedArg A.Pattern]
     -- ^ The patterns.
  -> Type
     -- ^ The expected type.
  -> (Telescope -> Telescope -> [Term] -> [String] -> [Arg Pattern]
      -> Type -> Permutation -> TCM a)
     -- ^ Continuation.
  -> TCM a
checkLeftHandSide c ps a ret = do
  a <- normalise a
  let TelV tel0' b0 = telView a
  ps <- insertImplicitPatterns ps tel0'
  unless (size tel0' >= size ps) $ typeError $ TooManyArgumentsInLHS (size ps) a
  let tel0     = useNamesFromPattern ps tel0'   
      (as, bs) = splitAt (size ps) $ telToList tel0
      gamma    = telFromList as
      b        = telePi (telFromList bs) b0

      -- internal patterns start as all variables
      ips      = map (fmap (VarP . fst)) as

      problem  = Problem ps (idP $ size ps, ips) gamma

  reportSDoc "tc.lhs.top" 10 $
    vcat [ text "checking lhs:"
	 , nest 2 $ vcat
	   [ text "ps    =" <+> fsep (map prettyA ps)
	   , text "a     =" <+> prettyTCM a
	   , text "a'    =" <+> prettyTCM (telePi tel0  b0)
	   , text "a''   =" <+> prettyTCM (telePi tel0' b0)
           , text "xs    =" <+> text (show $ map (fst . unArg) as)
	   , text "tel0  =" <+> prettyTCM tel0
	   , text "b0    =" <+> prettyTCM b0
	   , text "gamma =" <+> prettyTCM gamma
	   , text "b     =" <+> addCtxTel gamma (prettyTCM b)
	   ]
	 ]

  let idsub = [ Var i [] | i <- [0..] ]

  (Problem ps (perm, qs) delta, sigma, dpi, asb) <- checkLHS problem idsub [] []
  let b' = substs sigma b

  noPatternMatchingOnCodata $
    zip (map (not . (== "_") . fst . unArg) as) qs

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
    mapM_ checkDotPattern dpi
    let rho = renamingR perm -- I'm not certain about this...
        Perm n _ = perm
        xs  = replicate (fromIntegral n) "h"
    ret gamma delta rho xs qs b' perm
  where
    checkLHS :: Problem -> [Term] -> [DotPatternInst] -> [AsBinding] ->
                TCM (Problem, [Term], [DotPatternInst], [AsBinding])
    checkLHS problem sigma dpi asb
      | isSolvedProblem problem = do
        problem <- insertImplicitProblem problem -- inserting implicit patterns preserves solvedness
        noShadowingOfConstructors c problem
        return (problem, sigma, dpi, asb)
      | otherwise               = do
        sp <- splitProblem =<< insertImplicitProblem problem
        reportSDoc "tc.lhs.top" 20 $ text "splitting completed"
        case sp of
          Left NothingToSplit   -> nothingToSplitError problem
          Left (SplitPanic err) -> __IMPOSSIBLE__

          -- Split on literal pattern
          Right (Split p0 xs (Arg h (LitFocus lit iph hix a)) p1) -> do

            -- plug the hole with a lit pattern
            let ip    = plugHole (LitP lit) iph
                iperm = expandP (fromIntegral hix) 0 $ fst (problemOutPat problem)

            -- substitute the literal in p1 and sigma and dpi and asb
            let delta1 = problemTel p0
                delta2 = absApp (fmap problemTel p1) (Lit lit)
                rho    = [ var i | i <- [0..size delta2 - 1] ]
                      ++ [ raise (size delta2) $ Lit lit ]
                      ++ [ var i | i <- [size delta2 ..] ]
                  where
                    var i = Var i []
                sigma'   = substs rho sigma
                dpi'     = substs rho dpi
                asb0     = substs rho asb
                ip'      = substs rho ip

            -- Compute the new problem
            let ps'      = problemInPat p0 ++ problemInPat (absBody p1)
                delta'   = abstract delta1 delta2
                problem' = Problem ps' (iperm, ip') delta'
                asb'     = raise (size delta2) (map (\x -> AsB x (Lit lit) a) xs) ++ asb0
            checkLHS problem' sigma' dpi' asb'

          -- Split on constructor pattern
          Right (Split p0 xs (Arg h
                  ( Focus { focusCon      = c
                          , focusConArgs  = qs
                          , focusRange    = r
                          , focusOutPat   = iph
                          , focusHoleIx   = hix
                          , focusDatatype = d
                          , focusParams   = vs
                          , focusIndices  = ws
                          }
                  )) p1
                ) -> traceCall (CheckPattern (A.ConP (PatRange r) (A.AmbQ [c]) qs)
                                             (problemTel p0)
                                             (El Prop $ Def (Delayed False d) $ vs ++ ws)) $ do

            let delta1 = problemTel p0

            reportSDoc "tc.lhs.top" 10 $ sep
              [ text "checking lhs"
              , nest 2 $ text "tel =" <+> prettyTCM (problemTel problem)
              ]

            reportSDoc "tc.lhs.split" 15 $ sep
              [ text "split problem"
              , nest 2 $ vcat
                [ text "delta1 = " <+> prettyTCM delta1
                , text "delta2 = " <+> prettyTCM (problemTel $ absBody p1)
                ]
              ]

            Con c' [] <- constructorForm =<< normalise (Con c [])
            c <- return $ c' `withRangeOf` c

            ca <- defType <$> getConstInfo c

            reportSDoc "tc.lhs.top" 20 $ nest 2 $ vcat
              [ text "ca =" <+> prettyTCM ca
              , text "vs =" <+> prettyList (map prettyTCM vs)
              ]

            -- Lookup the type of the constructor at the given parameters
            a <- normalise =<< (`piApply` vs) . defType <$> getConstInfo c

            -- It will end in an application of the datatype
            let TelV gamma' ca@(El _ (Def d' us)) = telView a

            -- This should be the same datatype as we split on
            unless (d == force d') $ typeError $ ShouldBeApplicationOf ca (force d')

            -- Insert implicit patterns
            qs' <- insertImplicitPatterns qs gamma'

            unless (size qs' == size gamma') $
              typeError $ WrongNumberOfConstructorArguments c (size gamma') (size qs')

            let gamma = useNamesFromPattern qs' gamma'

            -- Get the type of the datatype.
            da <- normalise =<< (`piApply` vs) . defType <$> getConstInfo d

            -- Compute the flexible variables
            let flex = flexiblePatterns (problemInPat p0 ++ qs')

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

            -- We should subsitute c ys for x in Δ₂ and sigma
            let ys     = teleArgs gamma
                delta2 = absApp (raise (size gamma) $ fmap problemTel p1) (Con c ys)
                rho0 = [ var i | i <- [0..size delta2 - 1] ]
                    ++ [ raise (size delta2) $ Con c ys ]
                    ++ [ var i | i <- [size delta2 + size gamma ..] ]
                  where
                    var i = Var i []
                sigma0 = substs rho0 sigma
                dpi0   = substs rho0 dpi
                asb0   = substs rho0 asb

            reportSDoc "tc.lhs.top" 15 $ addCtxTel (delta1 `abstract` gamma) $ nest 2 $ vcat
              [ text "delta2 =" <+> prettyTCM delta2
              , text "sub0   =" <+> brackets (fsep $ punctuate comma $ map (maybe (text "_") prettyTCM) sub0)
              ]
            reportSDoc "tc.lhs.top" 15 $ addCtxTel (delta1 `abstract` gamma `abstract` delta2) $
              nest 2 $ vcat
                [ text "dpi0 = " <+> brackets (fsep $ punctuate comma $ map prettyTCM dpi0)
                , text "asb0 = " <+> brackets (fsep $ punctuate comma $ map prettyTCM asb0)
                ]

            -- Plug the hole in the out pattern with c ys
            let ysp = map (fmap (VarP . fst)) $ telToList gamma
                ip  = plugHole (ConP c ysp) iph
                ip0 = substs rho0 ip

            -- Δ₁Γ ⊢ sub0, we need something in Δ₁ΓΔ₂
            -- Also needs to be padded with Nothing's to have the right length.
            let pad n xs x = xs ++ replicate (max 0 $ n - size xs) x
                newTel = problemTel p0 `abstract` (gamma `abstract` delta2)
                sub    = replicate (size delta2) Nothing ++
                         pad (size delta1 + size gamma) (raise (size delta2) sub0) Nothing

            reportSDoc "tc.lhs.top" 15 $ nest 2 $ vcat
              [ text "newTel =" <+> prettyTCM newTel
              , addCtxTel newTel $ text "sub =" <+> brackets (fsep $ punctuate comma $ map (maybe (text "_") prettyTCM) sub)
              , text "ip  =" <+> text (show ip)
              , text "ip0  = " <+> text (show ip0)
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

            -- Compute the new dot pattern instantiations
            let ps0'   = problemInPat p0 ++ qs' ++ problemInPat (absBody p1)
                newDpi = dotPatternInsts ps0' (substs rho sub) instTypes

            reportSDoc "tc.lhs.top" 15 $ nest 2 $ vcat
              [ text "subst rho sub =" <+> brackets (fsep $ punctuate comma $ map (maybe (text "_") prettyTCM) (substs rho sub))
              , text "ps0'  =" <+> brackets (fsep $ punctuate comma $ map prettyA ps0')
              ]

            -- The final dpis and asbs are the new ones plus the old ones substituted by ρ
            let dpi' = substs rho dpi0 ++ newDpi
                asb' = substs rho $ asb0 ++ raise (size delta2) (map (\x -> AsB x (Con c ys) ca) xs)

            reportSDoc "tc.lhs.top" 15 $ nest 2 $ vcat
              [ text "dpi' = " <+> brackets (fsep $ punctuate comma $ map prettyTCM dpi')
              , text "asb' = " <+> brackets (fsep $ punctuate comma $ map prettyTCM asb')
              ]

            -- Apply the substitution to the type
            let sigma'   = substs rho sigma0

            reportSDoc "tc.lhs.inst" 15 $
              nest 2 $ text "ps0 = " <+> brackets (fsep $ punctuate comma $ map prettyA ps0')

            -- Permute the in patterns
            let ps'  = permute perm ps0'

           -- Compute the new permutation of the out patterns. This is the composition of
            -- the new permutation with the expansion of the old permutation to
            -- reflect the split.
            let perm'  = expandP (fromIntegral hix) (size gamma) $ fst (problemOutPat problem)
                iperm' = perm `composeP` perm'

            -- Instantiate the out patterns
            let ip'    = instantiatePattern sub perm' ip0
                newip  = substs rho ip'

            -- Construct the new problem
            let problem' = Problem ps' (iperm', newip) delta'

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

            -- Continue splitting
            checkLHS problem' sigma' dpi' asb'

-- Ensures that we are not performing dependent pattern matching on
-- codata.

noPatternMatchingOnCodata
  :: MonadTCM tcm
  => [(Bool, Arg Pattern)]  -- ^ True stands for dependent pattern matching.
  -> tcm ()
noPatternMatchingOnCodata = mapM_ check . map (unArg . snd) . filter fst
  where
  check (VarP {})   = return ()
  check (DotP {})   = return ()
  check (LitP {})   = return ()  -- Literals are assumed not to be coinductive.
  check (ConP q ps) = do
    TelV _ t <- telView . defType <$> getConstInfo q
    c <- isCoinductive t
    case c of
      Nothing    -> __IMPOSSIBLE__
      Just False -> mapM_ (check . unArg) ps
      Just True  -> typeError DependentPatternMatchingOnCodata
