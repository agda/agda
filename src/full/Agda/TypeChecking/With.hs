{-# LANGUAGE NondecreasingIndentation #-}

module Agda.TypeChecking.With where

import Prelude hiding ((!!))

import Control.Monad
import Control.Monad.Writer (WriterT, runWriterT, tell)

import Data.Either
import qualified Data.List as List
import Data.Maybe
import Data.Foldable ( foldrM )

import Agda.Syntax.Common
import Agda.Syntax.Internal as I
import Agda.Syntax.Internal.Pattern
import qualified Agda.Syntax.Abstract as A
import Agda.Syntax.Abstract.Pattern as A
import Agda.Syntax.Abstract.Views
import Agda.Syntax.Info
import Agda.Syntax.Position

import Agda.TypeChecking.Monad
import Agda.TypeChecking.Reduce
import Agda.TypeChecking.Datatypes
import Agda.TypeChecking.EtaContract
import Agda.TypeChecking.Free
import Agda.TypeChecking.Patterns.Abstract
import Agda.TypeChecking.Pretty
import Agda.TypeChecking.Primitive ( getRefl )
import Agda.TypeChecking.Records
import Agda.TypeChecking.Substitute
import Agda.TypeChecking.Telescope
import Agda.TypeChecking.Telescope.Path

import Agda.TypeChecking.Abstract
import Agda.TypeChecking.Rules.LHS.Implicit
import Agda.TypeChecking.Rules.LHS.Problem (ProblemEq(..))

import Agda.Utils.Functor
import Agda.Utils.List
import qualified Agda.Utils.List1 as List1
import Agda.Utils.Maybe
import Agda.Utils.Monad
import Agda.Utils.Null (empty)
import Agda.Utils.Permutation
import Agda.Utils.Pretty (prettyShow)
import qualified Agda.Utils.Pretty as P
import Agda.Utils.Size

import Agda.Utils.Impossible

-- | Split pattern variables according to with-expressions.

--   Input:
--
--   [@Δ@]         context of types and with-arguments.
--
--   [@Δ ⊢ t@]     type of rhs.
--
--   [@Δ ⊢ vs : as@]    with arguments and their types
--
--   Output:
--
--   [@Δ₁@]              part of context needed for with arguments and their types.
--
--   [@Δ₂@]              part of context not needed for with arguments and their types.
--
--   [@π@]               permutation from Δ to Δ₁Δ₂ as returned by 'splitTelescope'.
--
--   [@Δ₁Δ₂ ⊢ t'@]       type of rhs under @π@
--
--   [@Δ₁ ⊢ vs' : as'@]  with-arguments and their types depending only on @Δ₁@.

splitTelForWith
  -- Input:
  :: Telescope                         -- ^ __@Δ@__             context of types and with-arguments.
  -> Type                              -- ^ __@Δ ⊢ t@__         type of rhs.
  -> [Arg (Term, EqualityView)]        -- ^ __@Δ ⊢ vs : as@__   with arguments and their types.
  -- Output:
  -> ( Telescope                         -- @Δ₁@             part of context needed for with arguments and their types.
     , Telescope                         -- @Δ₂@             part of context not needed for with arguments and their types.
     , Permutation                       -- @π@              permutation from Δ to Δ₁Δ₂ as returned by 'splitTelescope'.
     , Type                              -- @Δ₁Δ₂ ⊢ t'@      type of rhs under @π@
     , [Arg (Term, EqualityView)]        -- @Δ₁ ⊢ vs' : as'@ with- and rewrite-arguments and types under @π@.
     )              -- ^ (__@Δ₁@__,__@Δ₂@__,__@π@__,__@t'@__,__@vtys'@__) where
--
--   [@Δ₁@]        part of context needed for with arguments and their types.
--
--   [@Δ₂@]        part of context not needed for with arguments and their types.
--
--   [@π@]         permutation from Δ to Δ₁Δ₂ as returned by 'splitTelescope'.
--
--   [@Δ₁Δ₂ ⊢ t'@] type of rhs under @π@
--
--   [@Δ₁ ⊢ vtys'@]  with-arguments and their types under @π@.

splitTelForWith delta t vtys = let
    -- Split the telescope into the part needed to type the with arguments
    -- and all the other stuff.
    fv = allFreeVars vtys
    SplitTel delta1 delta2 perm = splitTelescope fv delta

    -- Δ₁Δ₂ ⊢ π : Δ
    pi = renaming impossible (reverseP perm)
    -- Δ₁ ⊢ ρ : Δ₁Δ₂  (We know that as does not depend on Δ₂.)
    rho = strengthenS impossible $ size delta2
    -- Δ₁ ⊢ ρ ∘ π : Δ
    rhopi = composeS rho pi

    -- We need Δ₁Δ₂ ⊢ t'
    t' = applySubst pi t
    -- and Δ₁ ⊢ vtys'
    vtys' = applySubst rhopi vtys

  in (delta1, delta2, perm, t', vtys')


-- | Abstract with-expressions @vs@ to generate type for with-helper function.
--
-- Each @EqualityType@, coming from a @rewrite@, will turn into 2 abstractions.

withFunctionType
  :: Telescope                          -- ^ @Δ₁@                        context for types of with types.
  -> [Arg (Term, EqualityView)]         -- ^ @Δ₁,Δ₂ ⊢ vs : raise Δ₂ as@  with and rewrite-expressions and their type.
  -> Telescope                          -- ^ @Δ₁ ⊢ Δ₂@                   context extension to type with-expressions.
  -> Type                               -- ^ @Δ₁,Δ₂ ⊢ b@                 type of rhs.
  -> [(Int,(Term,Term))]                -- ^ @Δ₁,Δ₂ ⊢ [(i,(u0,u1))] : b  boundary.
  -> TCM (Type, Nat)
    -- ^ @Δ₁ → wtel → Δ₂′ → b′@ such that
    --     @[vs/wtel]wtel = as@ and
    --     @[vs/wtel]Δ₂′ = Δ₂@ and
    --     @[vs/wtel]b′ = b@.
    -- Plus the final number of with-arguments.
withFunctionType delta1 vtys delta2 b bndry = addContext delta1 $ do

  reportSLn "tc.with.abstract" 20 $ "preparing for with-abstraction"

  -- Normalize and η-contract the type @b@ of the rhs and the types @delta2@
  -- of the pattern variables not mentioned in @vs : as@.
  let dbg n s x = reportSDoc "tc.with.abstract" n $ nest 2 $ text (s ++ " =") <+> prettyTCM x

  d2b <- telePiPath_ delta2 b bndry
  dbg 30 "Δ₂ → B" d2b
  d2b  <- normalise d2b
  dbg 30 "normal Δ₂ → B" d2b
  d2b  <- etaContract d2b
  dbg 30 "eta-contracted Δ₂ → B" d2b

  vtys <- etaContract =<< normalise vtys

  -- wd2db = wtel → [vs : as] (Δ₂ → B)
  wd2b <- foldrM piAbstract d2b vtys
  dbg 30 "wΓ → Δ₂ → B" wd2b

  let nwithargs = countWithArgs (map (snd . unArg) vtys)

  TelV wtel _ <- telViewUpTo nwithargs wd2b

  -- select the boundary for "Δ₁" abstracting over "wΓ.Δ₂"
  let bndry' = [(i - sd2,(lams u0, lams u1)) | (i,(u0,u1)) <- bndry, i >= sd2]
        where sd2 = size delta2
              lams u = teleNoAbs wtel (abstract delta2 u)

  d1wd2b <- telePiPath_ delta1 wd2b bndry'

  dbg 30 "Δ₁ → wΓ → Δ₂ → B" d1wd2b

  return (d1wd2b, nwithargs)

countWithArgs :: [EqualityView] -> Nat
countWithArgs = sum . map countArgs
  where
    countArgs OtherType{}    = 1
    countArgs IdiomType{}    = 2
    countArgs EqualityType{} = 2

-- | From a list of @with@ and @rewrite@ expressions and their types,
--   compute the list of final @with@ expressions (after expanding the @rewrite@s).
withArguments :: [Arg (Term, EqualityView)] ->
                 TCM [Arg Term]
withArguments vtys = do
  tss <- forM vtys $ \ (Arg info ts) -> fmap (map (Arg info)) $ case ts of
    (v, OtherType a) -> pure [v]
    (prf, eqt@(EqualityType s _eq _pars _t v _v')) -> pure [unArg v, prf]
    (v, IdiomType t) -> do
       mkRefl <- getRefl
       pure [v, mkRefl (defaultArg v)]
  pure (concat tss)

-- | Compute the clauses for the with-function given the original patterns.
buildWithFunction
  :: [Name]               -- ^ Names of the module parameters of the parent function.
  -> QName                -- ^ Name of the parent function.
  -> QName                -- ^ Name of the with-function.
  -> Type                 -- ^ Types of the parent function.
  -> Telescope            -- ^ Context of parent patterns.
  -> [NamedArg DeBruijnPattern] -- ^ Parent patterns.
  -> Nat                  -- ^ Number of module parameters in parent patterns
  -> Substitution         -- ^ Substitution from parent lhs to with function lhs
  -> Permutation          -- ^ Final permutation.
  -> Nat                  -- ^ Number of needed vars.
  -> Nat                  -- ^ Number of with expressions.
  -> [A.SpineClause]      -- ^ With-clauses.
  -> TCM [A.SpineClause]  -- ^ With-clauses flattened wrt. parent patterns.
buildWithFunction cxtNames f aux t delta qs npars withSub perm n1 n cs = mapM buildWithClause cs
  where
    -- Nested with-functions will iterate this function once for each parent clause.
    buildWithClause (A.Clause (A.SpineLHS i _ allPs) inheritedPats rhs wh catchall) = do
      let (ps, wps)    = splitOffTrailingWithPatterns allPs
          (wps0, wps1) = splitAt n wps
          ps0          = map (updateNamedArg fromWithP) wps0
            where
            fromWithP (A.WithP _ p) = p
            fromWithP _ = __IMPOSSIBLE__
      reportSDoc "tc.with" 50 $ "inheritedPats:" <+> vcat
        [ prettyA p <+> "=" <+> prettyTCM v <+> ":" <+> prettyTCM a
        | A.ProblemEq p v a <- inheritedPats
        ]
      (strippedPats, ps') <- stripWithClausePatterns cxtNames f aux t delta qs npars perm ps
      reportSDoc "tc.with" 50 $ hang "strippedPats:" 2 $
                                  vcat [ prettyA p <+> "==" <+> prettyTCM v <+> (":" <+> prettyTCM t)
                                       | A.ProblemEq p v t <- strippedPats ]
      rhs <- buildRHS strippedPats rhs
      let (ps1, ps2) = splitAt n1 ps'
      let result = A.Clause (A.SpineLHS i aux $ ps1 ++ ps0 ++ ps2 ++ wps1)
                     (inheritedPats ++ strippedPats)
                     rhs wh catchall
      reportSDoc "tc.with" 20 $ vcat
        [ "buildWithClause returns" <+> prettyA result
        ]
      return result

    buildRHS _ rhs@A.RHS{}                 = return rhs
    buildRHS _ rhs@A.AbsurdRHS             = return rhs
    buildRHS _ (A.WithRHS q es cs)         = A.WithRHS q es <$>
      mapM ((A.spineToLhs . permuteNamedDots) <.> buildWithClause . A.lhsToSpine) cs
    buildRHS strippedPats1 (A.RewriteRHS qes strippedPats2 rhs wh) =
      flip (A.RewriteRHS qes (applySubst withSub $ strippedPats1 ++ strippedPats2)) wh <$> buildRHS [] rhs

    -- The stripped patterns computed by buildWithClause lives in the context
    -- of the top with-clause (of the current call to buildWithFunction). When
    -- we recurse we expect inherited patterns to live in the context
    -- of the innermost parent clause. Note that this makes them live in the
    -- context of the with-function arguments before any pattern matching. We
    -- need to update again once the with-clause patterns have been checked.
    -- This happens in Rules.Def.checkClause before calling checkRHS.
    permuteNamedDots :: A.SpineClause -> A.SpineClause
    permuteNamedDots (A.Clause lhs strippedPats rhs wh catchall) =
      A.Clause lhs (applySubst withSub strippedPats) rhs wh catchall


-- The arguments of @stripWithClausePatterns@ are documented
-- at its type signature.
-- The following is duplicate information, but may help reading the examples below.
--
-- [@Δ@]   context bound by lhs of original function.
-- [@f@]   name of @with@-function.
-- [@t@]   type of the original function.
-- [@qs@]  internal patterns for original function.
-- [@np@]  number of module parameters in @qs@
-- [@π@]   permutation taking @vars(qs)@ to @support(Δ)@.
-- [@ps@]  patterns in with clause (eliminating type @t@).
-- [@ps'@] patterns for with function (presumably of type @Δ@).

{-| @stripWithClausePatterns cxtNames parent f t Δ qs np π ps = ps'@

Example:

@
  record Stream (A : Set) : Set where
    coinductive
    constructor delay
    field       force : A × Stream A

  record SEq (s t : Stream A) : Set where
    coinductive
    field
      ~force : let a , as = force s
                   b , bs = force t
               in  a ≡ b × SEq as bs

  test : (s : Nat × Stream Nat) (t : Stream Nat) → SEq (delay s) t → SEq t (delay s)
  ~force (test (a     , as) t p) with force t
  ~force (test (suc n , as) t p) | b , bs = ?
@

With function:

@
  f : (t : Stream Nat) (w : Nat × Stream Nat) (a : Nat) (as : Stream Nat)
      (p : SEq (delay (a , as)) t) → (fst w ≡ a) × SEq (snd w) as

  Δ  = t a as p   -- reorder to bring with-relevant (= needed) vars first
  π  = a as t p → Δ
  qs = (a     , as) t p ~force
  ps = (suc n , as) t p ~force
  ps' = (suc n) as t p
@

Resulting with-function clause is:

@
  f t (b , bs) (suc n) as t p
@

Note: stripWithClausePatterns factors __@ps@__ through __@qs@__, thus

@
  ps = qs[ps']
@

where @[..]@ is to be understood as substitution.
The projection patterns have vanished from __@ps'@__ (as they are already in __@qs@__).
-}

stripWithClausePatterns
  :: [Name]                   -- ^ __@cxtNames@__ names of the module parameters of the parent function
  -> QName                    -- ^ __@parent@__ name of the parent function.
  -> QName                    -- ^ __@f@__   name of with-function.
  -> Type                     -- ^ __@t@__   top-level type of the original function.
  -> Telescope                -- ^ __@Δ@__   context of patterns of parent function.
  -> [NamedArg DeBruijnPattern] -- ^ __@qs@__  internal patterns for original function.
  -> Nat                      -- ^ __@npars@__ number of module parameters in @qs@.
  -> Permutation              -- ^ __@π@__   permutation taking @vars(qs)@ to @support(Δ)@.
  -> [NamedArg A.Pattern]     -- ^ __@ps@__  patterns in with clause (eliminating type @t@).
  -> TCM ([A.ProblemEq], [NamedArg A.Pattern]) -- ^ __@ps'@__ patterns for with function (presumably of type @Δ@).
stripWithClausePatterns cxtNames parent f t delta qs npars perm ps = do
  -- Andreas, 2014-03-05 expand away pattern synoyms (issue 1074)
  ps <- expandPatternSynonyms ps
  -- Ulf, 2016-11-16 Issue 2303: We need the module parameter
  -- instantiations from qs, so we make sure
  -- that t is the top-level type of the parent function and add patterns for
  -- the module parameters to ps before stripping.
  let paramPat i _ = A.VarP $ A.mkBindName $ indexWithDefault __IMPOSSIBLE__ cxtNames i
      ps' = zipWith (fmap . fmap . paramPat) [0..] (take npars qs) ++ ps
  psi <- insertImplicitPatternsT ExpandLast ps' t
  reportSDoc "tc.with.strip" 10 $ vcat
    [ "stripping patterns"
    , nest 2 $ "t   = " <+> prettyTCM t
    , nest 2 $ "ps  = " <+> fsep (punctuate comma $ map prettyA ps)
    , nest 2 $ "ps' = " <+> fsep (punctuate comma $ map prettyA ps')
    , nest 2 $ "psi = " <+> fsep (punctuate comma $ map prettyA psi)
    , nest 2 $ "qs  = " <+> fsep (punctuate comma $ map (prettyTCM . namedArg) qs)
    , nest 2 $ "perm= " <+> text (show perm)
    ]

  -- Andreas, 2015-11-09 Issue 1710: self starts with parent-function, not with-function!
  (ps', strippedPats) <- runWriterT $ strip (Def parent []) t psi qs
  reportSDoc "tc.with.strip" 50 $ nest 2 $
    "strippedPats:" <+> vcat [ prettyA p <+> "=" <+> prettyTCM v <+> ":" <+> prettyTCM a | A.ProblemEq p v a <- strippedPats ]
  let psp = permute perm ps'
  reportSDoc "tc.with.strip" 10 $ vcat
    [ nest 2 $ "ps' = " <+> fsep (punctuate comma $ map prettyA ps')
    , nest 2 $ "psp = " <+> fsep (punctuate comma $ map prettyA $ psp)
    ]
  return (strippedPats, psp)
  where

    -- We need to get the correct hiding from the lhs context. The unifier may have moved bindings
    -- sites around so we can't trust the hiding of the parent pattern variables. We should preserve
    -- the origin though.
    varArgInfo = \ x -> let n = dbPatVarIndex x in
                        if n < length infos then infos !! n else __IMPOSSIBLE__
      where infos = reverse $ map getArgInfo $ telToList delta

    setVarArgInfo x p = setOrigin (getOrigin p) $ setArgInfo (varArgInfo x) p

    strip
      :: Term                         -- Self.
      -> Type                         -- The type to be eliminated.
      -> [NamedArg A.Pattern]         -- With-clause patterns.
      -> [NamedArg DeBruijnPattern]   -- Parent-clause patterns with de Bruijn indices relative to Δ.
      -> WriterT [ProblemEq] TCM [NamedArg A.Pattern]
            -- With-clause patterns decomposed by parent-clause patterns.
            -- Also outputs named dot patterns from the parent clause that
            -- we need to add let-bindings for.

    -- Case: out of with-clause patterns.
    strip self t [] qs@(_ : _) = do
      reportSDoc "tc.with.strip" 15 $ vcat
        [ "strip (out of A.Patterns)"
        , nest 2 $ "qs  =" <+> fsep (punctuate comma $ map (prettyTCM . namedArg) qs)
        , nest 2 $ "self=" <+> prettyTCM self
        , nest 2 $ "t   =" <+> prettyTCM t
        ]
      -- Andreas, 2015-06-11, issue 1551:
      -- As the type t develops, we need to insert more implicit patterns,
      -- due to copatterns / flexible arity.
      ps <- liftTCM $ insertImplicitPatternsT ExpandLast [] t
      if null ps then
        typeError $ GenericError $ "Too few arguments given in with-clause"
       else strip self t ps qs

    -- Case: out of parent-clause patterns.
    -- This is only ok if all remaining with-clause patterns
    -- are implicit patterns (we inserted too many).
    strip _ _ ps      []      = do
      let implicit (A.WildP{})     = True
          implicit (A.ConP ci _ _) = conPatOrigin ci == ConOSystem
          implicit _               = False
      unless (all (implicit . namedArg) ps) $
        typeError $ GenericError $ "Too many arguments given in with-clause"
      return []

    -- Case: both parent-clause pattern and with-clause pattern present.
    -- Make sure they match, and decompose into subpatterns.
    strip self t (p0 : ps) qs@(q : _)
      | A.AsP _ x p <- namedArg p0 = do
        (a, _) <- mustBePi t
        let v = patternToTerm (namedArg q)
        tell [ProblemEq (A.VarP x) v a]
        strip self t (fmap (p <$) p0 : ps) qs
    strip self t ps0@(p0 : ps) qs0@(q : qs) = do
      p <- liftTCM $ (traverse . traverse) expandLitPattern p0
      reportSDoc "tc.with.strip" 15 $ vcat
        [ "strip"
        , nest 2 $ "ps0 =" <+> fsep (punctuate comma $ map prettyA ps0)
        , nest 2 $ "exp =" <+> prettyA p
        , nest 2 $ "qs0 =" <+> fsep (punctuate comma $ map (prettyTCM . namedArg) qs0)
        , nest 2 $ "self=" <+> prettyTCM self
        , nest 2 $ "t   =" <+> prettyTCM t
        ]
      case namedArg q of
        ProjP o d -> case A.isProjP p of
          Just (o', AmbQ ds) -> do
            -- We assume here that neither @o@ nor @o'@ can be @ProjSystem@.
            if o /= o' then liftTCM $ mismatchOrigin o o' else do
            -- Andreas, 2016-12-28, issue #2360:
            -- We disambiguate the projection in the with clause
            -- to the projection in the parent clause.
            d  <- liftTCM $ getOriginalProjection d
            found <- anyM ds $ \ d' -> liftTCM $ (Just d ==) . fmap projOrig <$> isProjection d'
            if not found then mismatch else do
              (self1, t1, ps) <- liftTCM $ do
                t <- reduce t
                (_, self1, t1) <- fromMaybe __IMPOSSIBLE__ <$> projectTyped self t o d
                -- Andreas, 2016-01-21, issue #1791
                -- The type of a field might start with hidden quantifiers.
                -- So we may have to insert more implicit patterns here.
                ps <- insertImplicitPatternsT ExpandLast ps t1
                return (self1, t1, ps)
              strip self1 t1 ps qs
          Nothing -> mismatch

        -- We can safely strip dots from variables. The unifier will put them back when required.
        VarP _ x | A.DotP _ u <- namedArg p
                 , A.Var y <- unScope u -> do
          (setVarArgInfo x (setNamedArg p $ A.VarP $ A.mkBindName y) :) <$>
            recurse (var (dbPatVarIndex x))

        VarP _ x  ->
          (setVarArgInfo x p :) <$> recurse (var (dbPatVarIndex x))

        IApplyP _ _ _ x  ->
          (setVarArgInfo x p :) <$> recurse (var (dbPatVarIndex x))

        DefP{}  -> typeError $ GenericError $ "with clauses not supported in the presence of hcomp patterns" -- TODO this should actually be impossible

        DotP i v  -> do
          (a, _) <- mustBePi t
          tell [ProblemEq (namedArg p) v a]
          case v of
            Var x [] | PatOVar{} <- patOrigin i
               -> (p :) <$> recurse (var x)
            _  -> (makeWildP p :) <$> recurse v

        q'@(ConP c ci qs') -> do
         reportSDoc "tc.with.strip" 60 $
           "parent pattern is constructor " <+> prettyTCM c
         (a, b) <- mustBePi t
         -- The type of the current pattern is a datatype.
         Def d es <- liftTCM $ reduce (unEl $ unDom a)
         let us = fromMaybe __IMPOSSIBLE__ $ allApplyElims es
         -- Get the original constructor and field names.
         c <- either __IMPOSSIBLE__ (`withRangeOf` c) <$> do liftTCM $ getConForm $ conName c

         case namedArg p of

          -- Andreas, 2015-07-07 Issue 1606.
          -- Agda sometimes changes a record of dot patterns into a dot pattern,
          -- so the user should be allowed to do likewise.
          -- Jesper, 2017-11-16. This is now also allowed for data constructors.
          A.DotP r e -> do
            tell [ProblemEq (A.DotP r e) (patternToTerm q') a]
            ps' <-
              case appView e of
                -- If dot-pattern is an application of the constructor, try to preserve the
                -- arguments.
                Application (A.Con (A.AmbQ cs')) es -> do
                  cs' <- liftTCM $ List1.rights <$> mapM getConForm cs'
                  unless (c `elem` cs') mismatch
                  return $ (map . fmap . fmap) (A.DotP r) es
                _  -> return $ map (unnamed (A.WildP empty) <$) qs'
            stripConP d us b c ConOCon qs' ps'

          -- Andreas, 2016-12-29, issue #2363.
          -- Allow _ to stand for the corresponding parent pattern.
          A.WildP{} -> do
            -- Andreas, 2017-10-13, issue #2803:
            -- Delete the name, since it can confuse insertImplicitPattern.
            let ps' = map (unnamed (A.WildP empty) <$) qs'
            stripConP d us b c ConOCon qs' ps'

          -- Jesper, 2018-05-13, issue #2998.
          -- We also allow turning a constructor pattern into a variable.
          -- In general this is not type-safe since the types of some variables
          -- in the constructor pattern may have changed, so we have to
          -- re-check these solutions when checking the with clause (see LHS.hs)
          A.VarP x -> do
            tell [ProblemEq (A.VarP x) (patternToTerm q') a]
            let ps' = map (unnamed (A.WildP empty) <$) qs'
            stripConP d us b c ConOCon qs' ps'

          A.ConP _ (A.AmbQ cs') ps' -> do
            -- Check whether the with-clause constructor can be (possibly trivially)
            -- disambiguated to be equal to the parent-clause constructor.
            -- Andreas, 2017-08-13, herein, ignore abstract constructors.
            cs' <- liftTCM $ List1.rights <$> mapM getConForm cs'
            unless (c `elem` cs') mismatch
            -- Strip the subpatterns ps' and then continue.
            stripConP d us b c ConOCon qs' ps'

          A.RecP _ fs -> caseMaybeM (liftTCM $ isRecord d) mismatch $ \ def -> do
            ps' <- liftTCM $ insertMissingFieldsFail d (const $ A.WildP empty) fs
                                                 (map argFromDom $ recordFieldNames def)
            stripConP d us b c ConORec qs' ps'

          p@(A.PatternSynP pi' c' ps') -> do
             reportSDoc "impossible" 10 $
               "stripWithClausePatterns: encountered pattern synonym " <+> prettyA p
             __IMPOSSIBLE__

          p -> do
           reportSDoc "tc.with.strip" 60 $
             text $ "with clause pattern is  " ++ show p
           mismatch

        LitP _ lit -> case namedArg p of
          A.LitP _ lit' | lit == lit' -> recurse $ Lit lit
          A.WildP{}                   -> recurse $ Lit lit

          p@(A.PatternSynP pi' c' [ps']) -> do
             reportSDoc "impossible" 10 $
               "stripWithClausePatterns: encountered pattern synonym " <+> prettyA p
             __IMPOSSIBLE__

          _ -> mismatch
      where
        recurse v = do
          -- caseMaybeM (liftTCM $ isPath t) (return ()) $ \ _ ->
          --   typeError $ GenericError $
          --     "With-clauses currently not supported under Path abstraction."

          let piOrPathApplyM t v = do
                (TelV tel t', bs) <- telViewUpToPathBoundaryP 1 t
                unless (size tel == 1) $ __IMPOSSIBLE__
                return (teleElims tel bs, subst 0 v t')
          (e, t') <- piOrPathApplyM t v
          strip (self `applyE` e) t' ps qs

        mismatch :: forall m a. (MonadAddContext m, MonadTCError m) => m a
        mismatch = addContext delta $ typeError $
          WithClausePatternMismatch (namedArg p0) q
        mismatchOrigin o o' = addContext delta . typeError . GenericDocError =<< fsep
          [ "With clause pattern"
          , prettyA p0
          , "is not an instance of its parent pattern"
          , P.fsep <$> prettyTCMPatterns [q]
          , text $ "since the parent pattern is " ++ prettyProjOrigin o ++
                   " and the with clause pattern is " ++ prettyProjOrigin o'
          ]
        prettyProjOrigin ProjPrefix  = "a prefix projection"
        prettyProjOrigin ProjPostfix = "a postfix projection"
        prettyProjOrigin ProjSystem  = __IMPOSSIBLE__

        -- Make a WildP, keeping arg. info.
        makeWildP :: NamedArg A.Pattern -> NamedArg A.Pattern
        makeWildP = updateNamedArg $ const $ A.WildP patNoRange

        -- case I.ConP / A.ConP
        stripConP
          :: QName       -- Data type name of this constructor pattern.
          -> [Arg Term]  -- Data type arguments of this constructor pattern.
          -> Abs Type    -- Type the remaining patterns eliminate.
          -> ConHead     -- Constructor of this pattern.
          -> ConInfo     -- Constructor info of this pattern (constructor/record).
          -> [NamedArg DeBruijnPattern]  -- Argument patterns (parent clause).
          -> [NamedArg A.Pattern]        -- Argument patterns (with clause).
          -> WriterT [ProblemEq] TCM [NamedArg A.Pattern]  -- Stripped patterns.
        stripConP d us b c ci qs' ps' = do

          -- Get the type and number of parameters of the constructor.
          Defn {defType = ct, theDef = Constructor{conPars = np}}  <- getConInfo c
          -- Compute the argument telescope for the constructor
          let ct' = ct `piApply` take np us
          TelV tel' _ <- liftTCM $ telViewPath ct'
          -- (TelV tel' _, _boundary) <- liftTCM $ telViewPathBoundaryP ct'

          reportSDoc "tc.with.strip" 20 $
            vcat [ "ct  = " <+> prettyTCM ct
                 , "ct' = " <+> prettyTCM ct'
                 , "np  = " <+> text (show np)
                 , "us  = " <+> prettyList (map prettyTCM us)
                 , "us' = " <+> prettyList (map prettyTCM $ take np us)
                 ]

          -- TODO Andrea: preserve IApplyP patterns in v, see _boundary?
          -- Compute the new type
          let v  = Con c ci [ Apply $ Arg info (var i) | (i, Arg info _) <- zip (downFrom $ size qs') qs' ]
              t' = tel' `abstract` absApp (raise (size tel') b) v
              self' = tel' `abstract` apply1 (raise (size tel') self) v  -- Issue 1546

          reportSDoc "tc.with.strip" 15 $ sep
            [ "inserting implicit"
            , nest 2 $ prettyList $ map prettyA (ps' ++ ps)
            , nest 2 $ ":" <+> prettyTCM t'
            ]

          -- Insert implicit patterns (just for the constructor arguments)
          psi' <- liftTCM $ insertImplicitPatterns ExpandLast ps' tel'
          unless (size psi' == size tel') $ typeError $
            WrongNumberOfConstructorArguments (conName c) (size tel') (size psi')

          -- Andreas, Ulf, 2016-06-01, Ulf's variant at issue #679
          -- Since instantiating the type with a constructor pattern
          -- can reveal more hidden arguments, we need to insert them here.
          psi <- liftTCM $ insertImplicitPatternsT ExpandLast (psi' ++ ps) t'

          -- Keep going
          strip self' t' psi (qs' ++ qs)

-- | Construct the display form for a with function. It will display
--   applications of the with function as applications to the original function.
--   For instance,
--
--   @
--     aux a b c
--   @
--
--   as
--
--   @
--     f (suc a) (suc b) | c
--   @
withDisplayForm
  :: QName
       -- ^ The name of parent function.
  -> QName
       -- ^ The name of the @with@-function.
  -> Telescope
       -- ^ __@Δ₁@__     The arguments of the @with@ function before the @with@ expressions.
  -> Telescope
       -- ^ __@Δ₂@__     The arguments of the @with@ function after the @with@ expressions.
  -> Nat
       -- ^ __@n@__      The number of @with@ expressions.
  -> [NamedArg DeBruijnPattern]
      -- ^ __@qs@__      The parent patterns.
  -> Permutation
      -- ^ __@perm@__    Permutation to split into needed and unneeded vars.
  -> Permutation
      -- ^ __@lhsPerm@__ Permutation reordering the variables in parent patterns.
  -> TCM DisplayForm
withDisplayForm f aux delta1 delta2 n qs perm@(Perm m _) lhsPerm = do

  -- Compute the arity of the display form.
  let arity0 = n + size delta1 + size delta2
  -- The currently free variables have to be added to the front.
  topArgs <- raise arity0 <$> getContextArgs
  let top    = length topArgs
      arity  = arity0 + top

  -- Build the rhs of the display form.
  wild <- freshNoName_ <&> \ x -> Def (qualify_ x) []
  let -- Convert the parent patterns to terms.
      tqs0       = patsToElims qs
      -- Build a substitution to replace the parent pattern vars
      -- by the pattern vars of the with-function.
      (ys0, ys1) = splitAt (size delta1) $ permute perm $ downFrom m
      ys         = reverse (map Just ys0 ++ replicate n Nothing ++ map Just ys1)
                   ++ map (Just . (m +)) [0..top-1]
      rho        = sub top ys wild
      tqs        = applySubst rho tqs0
      -- Build the arguments to the with function.
      es         = map (Apply . fmap DTerm) topArgs ++ tqs
      withArgs   = map var $ take n $ downFrom $ size delta2 + n
      dt         = DWithApp (DDef f es) (map DTerm withArgs) []

  -- Build the lhs of the display form and finish.
  -- @var 0@ is the pattern variable (hole).
  let display = Display arity [Apply $ defaultArg $ var i | i <- downFrom arity] dt

  -- Debug printing.
  let addFullCtx = addContext delta1
                 . flip (foldr addContext) (for [1..n] $ \ i -> "w" ++ show i)
                 . addContext delta2
  reportSDoc "tc.with.display" 20 $ vcat
    [ "withDisplayForm"
    , nest 2 $ vcat
      [ "f      =" <+> text (prettyShow f)
      , "aux    =" <+> text (prettyShow aux)
      , "delta1 =" <+> prettyTCM delta1
      , "delta2 =" <+> do addContext delta1 $ prettyTCM delta2
      , "n      =" <+> text (show n)
      , "perm   =" <+> text (show perm)
      , "top    =" <+> do addFullCtx $ prettyTCM topArgs
      , "qs     =" <+> prettyList (map pretty qs)
      , "qsToTm =" <+> prettyTCM tqs0 -- ctx would be permuted form of delta1 ++ delta2
      , "ys     =" <+> text (show ys)
      , "rho    =" <+> text (prettyShow rho)
      , "qs[rho]=" <+> do addFullCtx $ prettyTCM tqs
      , "dt     =" <+> do addFullCtx $ prettyTCM dt
      ]
    ]
  reportSDoc "tc.with.display" 70 $ nest 2 $ vcat
      [ "raw    =" <+> text (show display)
      ]

  return display
  where
    -- Ulf, 2014-02-19: We need to rename the module parameters as well! (issue1035)
    -- sub top ys wild = map term [0 .. m - 1] ++# raiseS (length qs)
    -- Andreas, 2015-10-28: Yes, but properly! (Issue 1407)
    sub top ys wild = parallelS $ map term [0 .. m + top - 1]
      where
        term i = maybe wild var $ List.elemIndex (Just i) ys

-- Andreas, 2014-12-05 refactored using numberPatVars
-- Andreas, 2013-02-28 modeled after Coverage/Match/buildMPatterns
patsToElims :: [NamedArg DeBruijnPattern] -> [I.Elim' DisplayTerm]
patsToElims = map $ toElim . fmap namedThing
  where
    toElim :: Arg DeBruijnPattern -> I.Elim' DisplayTerm
    toElim (Arg ai p) = case p of
      ProjP o d -> I.Proj o d
      p         -> I.Apply $ Arg ai $ toTerm p

    toTerms :: [NamedArg DeBruijnPattern] -> [Arg DisplayTerm]
    toTerms = map $ fmap $ toTerm . namedThing

    toTerm :: DeBruijnPattern -> DisplayTerm
    toTerm p = case patOrigin $ fromMaybe __IMPOSSIBLE__ $ patternInfo p of
      PatOSystem -> toDisplayPattern p
      PatOSplit  -> toDisplayPattern p
      PatOVar{}  -> toVarOrDot p
      PatODot    -> DDot $ patternToTerm p
      PatOWild   -> toVarOrDot p
      PatOCon    -> toDisplayPattern p
      PatORec    -> toDisplayPattern p
      PatOLit    -> toDisplayPattern p
      PatOAbsurd -> toDisplayPattern p -- see test/Succeed/Issue2849.agda

    toDisplayPattern :: DeBruijnPattern -> DisplayTerm
    toDisplayPattern = \case
      IApplyP _ _ _ x -> DTerm $ var $ dbPatVarIndex x -- TODO, should be an Elim' DisplayTerm ?
      ProjP _ d  -> __IMPOSSIBLE__
      VarP i x -> DTerm  $ var $ dbPatVarIndex x
      DotP i t -> DDot   $ t
      p@(ConP c cpi ps) -> DCon c (fromConPatternInfo cpi) $ toTerms ps
      LitP i l -> DTerm  $ Lit l
      DefP _ q ps -> DDef q $ map Apply $ toTerms ps

    toVarOrDot :: DeBruijnPattern -> DisplayTerm
    toVarOrDot p = case patternToTerm p of
      Var i [] -> DTerm $ var i
      t        -> DDot t
