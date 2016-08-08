{-# LANGUAGE CPP #-}
{-# LANGUAGE NondecreasingIndentation #-}

module Agda.TypeChecking.With where

import Control.Arrow ((&&&), (***), first, second)
import Control.Applicative hiding (empty)
import Control.Monad
import Control.Monad.Writer (WriterT, runWriterT, tell)

import Data.List
import Data.Maybe
import Data.Monoid
import Data.Traversable (traverse)

import Agda.Syntax.Common
import Agda.Syntax.Internal as I
import Agda.Syntax.Internal.Pattern
import qualified Agda.Syntax.Abstract as A
import Agda.Syntax.Abstract.Views
import Agda.Syntax.Info
import Agda.Syntax.Position

import Agda.TypeChecking.Monad
import Agda.TypeChecking.Monad.Builtin
import Agda.TypeChecking.Reduce
import Agda.TypeChecking.Datatypes
import Agda.TypeChecking.EtaContract
import Agda.TypeChecking.Free
import Agda.TypeChecking.Patterns.Abstract
import Agda.TypeChecking.Pretty
import Agda.TypeChecking.Records
import Agda.TypeChecking.Substitute
import Agda.TypeChecking.Telescope
import Agda.TypeChecking.ReconstructParameters

import Agda.TypeChecking.Abstract
import Agda.TypeChecking.Rules.LHS.Implicit
import Agda.TypeChecking.Rules.LHS (isFlexiblePattern)

import Agda.Utils.Functor
import Agda.Utils.List
import Agda.Utils.Maybe
import Agda.Utils.Monad
import Agda.Utils.Null (empty)
import Agda.Utils.Permutation
import Agda.Utils.Pretty (prettyShow)
import Agda.Utils.Size

#include "undefined.h"
import Agda.Utils.Impossible


-- | Split pattern variables according to with-expressions.

--   Input:
--
--   [@Δ@]         context of types and with-arguments.
--
--   [@Δ ⊢ t@]     type of rhs.
--
--   [@Δ ⊢ as@]    types of with arguments.
--
--   [@Δ ⊢ vs@]    with arguments.
--
--
--   Output:
--
--   [@Δ₁@]        part of context not needed for with arguments and their types.
--
--   [@Δ₂@]        part of context needed for with arguments and their types.
--
--   [@π@]         permutation from Δ to Δ₁Δ₂ as returned by 'splitTelescope'.
--
--   [@Δ₁Δ₂ ⊢ t'@] type of rhs under @π@
--
--   [@Δ₁ ⊢ as'@]  types with with-arguments depending only on @Δ₁@.
--
--   [@Δ₁ ⊢ vs'@]  with-arguments under @π@.

splitTelForWith
  -- Input:
  :: Telescope      -- ^ __@Δ@__        context of types and with-arguments.
  -> Type           -- ^ __@Δ ⊢ t@__    type of rhs.
  -> [EqualityView] -- ^ __@Δ ⊢ as@__   types of with arguments.
  -> [Term]         -- ^ __@Δ ⊢ vs@__   with arguments.
  -- Output:
  -> ( Telescope    -- @Δ₁@       part of context not needed for with arguments and their types.
     , Telescope    -- @Δ₂@       part of context needed for with arguments and their types.
     , Permutation  -- @π@        permutation from Δ to Δ₁Δ₂ as returned by 'splitTelescope'.
     , Type         -- @Δ₁Δ₂ ⊢ t'@ type of rhs under @π@
     , [EqualityView] -- @Δ₁ ⊢ as'@ types with with- and rewrite-arguments depending only on @Δ₁@.
     , [Term]       -- @Δ₁ ⊢ vs'@ with- and rewrite-arguments under @π@.
     )              -- ^ (__@Δ₁@__,__@Δ₂@__,__@π@__,__@t'@__,__@as'@__,__@vs'@__) where
--
--   [@Δ₁@]        part of context not needed for with arguments and their types.
--
--   [@Δ₂@]        part of context needed for with arguments and their types.
--
--   [@π@]         permutation from Δ to Δ₁Δ₂ as returned by 'splitTelescope'.
--
--   [@Δ₁Δ₂ ⊢ t'@] type of rhs under @π@
--
--   [@Δ₁ ⊢ as'@]  types with with-arguments depending only on @Δ₁@.
--
--   [@Δ₁ ⊢ vs'@]  with-arguments under @π@.

splitTelForWith delta t as vs = let
    -- Andreas, 2016-01-27, unfixing issue 1692
    -- Due to public protests, we do not rewrite in the types of rewrite
    -- expressions.
    -- Otherwise, we cannot rewrite twice after another with the same equation
    -- as it turns into a reflexive equation in the first rewrite.
    -- Thus we include the fvs of the rewrite terms in Δ₁.
    rewriteTerms = map snd $ filter (isEqualityType . fst) $ zip as vs

    -- Split the telescope into the part needed to type the with arguments
    -- and all the other stuff.
    fv = allFreeVars (as, vs)
    SplitTel delta1 delta2 perm = splitTelescope fv delta

    -- Δ₁Δ₂ ⊢ π : Δ
    pi = renaming __IMPOSSIBLE__ (reverseP perm)
    -- Δ₁ ⊢ ρ : Δ₁Δ₂  (We know that as does not depend on Δ₂.)
    rho = strengthenS __IMPOSSIBLE__ $ size delta2
    -- Δ₁ ⊢ ρ ∘ π : Δ
    rhopi = composeS rho pi

    -- We need Δ₁Δ₂ ⊢ t'
    t' = applySubst pi t
    -- and Δ₁ ⊢ as'
    as' = applySubst rhopi as
    -- and Δ₁ ⊢ vs' : as'
    vs' = applySubst rhopi vs

  in (delta1, delta2, perm, t', as', vs')


-- | Abstract with-expressions @vs@ to generate type for with-helper function.
--
-- Each @EqualityType@, coming from a @rewrite@, will turn into 2 abstractions.

withFunctionType
  :: Telescope  -- ^ @Δ₁@                       context for types of with types.
  -> [Term]     -- ^ @Δ₁,Δ₂ ⊢ vs : raise Δ₂ as@  with and rewrite-expressions.
  -> [EqualityView] -- ^ @Δ₁ ⊢ as@                  types of with and rewrite-expressions.
  -> Telescope  -- ^ @Δ₁ ⊢ Δ₂@                  context extension to type with-expressions.
  -> Type       -- ^ @Δ₁,Δ₂ ⊢ b@                type of rhs.
  -> TCM (Type, Nat)
    -- ^ @Δ₁ → wtel → Δ₂′ → b′@ such that
    --     @[vs/wtel]wtel = as@ and
    --     @[vs/wtel]Δ₂′ = Δ₂@ and
    --     @[vs/wtel]b′ = b@.
    -- Plus the final number of with-arguments.
withFunctionType delta1 vs as delta2 b = addContext delta1 $ do

  reportSLn "tc.with.abstract" 20 $ "preparing for with-abstraction"

  -- Normalize and η-contract the type @b@ of the rhs and the types @delta2@
  -- of the pattern variables not mentioned in @vs : as@.
  let dbg n s x = reportSDoc "tc.with.abstract" n $ nest 2 $ text (s ++ " =") <+> prettyTCM x

  let d2b = telePi_ delta2 b
  dbg 30 "Δ₂ → B" d2b
  d2b  <- normalise d2b
  dbg 30 "normal Δ₂ → B" d2b
  d2b  <- etaContract d2b
  dbg 30 "eta-contracted Δ₂ → B" d2b

  vs <- etaContract =<< normalise vs
  as <- etaContract =<< normalise as  -- do we need this?

  let piAbstractVs []         b = return b
      piAbstractVs (va : vas) b = piAbstract va =<< piAbstractVs vas b
  -- wd2db = wtel → [vs : as] (Δ₂ → B)
  wd2b <- piAbstractVs (zip vs as) d2b
  dbg 30 "wΓ → Δ₂ → B" wd2b

  return (telePi_ delta1 wd2b, countWithArgs as)

countWithArgs :: [EqualityView] -> Nat
countWithArgs = sum . map countArgs
  where
    countArgs OtherType{}    = 1
    countArgs EqualityType{} = 2

-- | From a list of @with@ and @rewrite@ expressions and their types,
--   compute the list of final @with@ expressions (after expanding the @rewrite@s).
withArguments :: [Term] -> [EqualityView] -> [Term]
withArguments vs as = concat $ for (zip vs as) $ \case
  (v, OtherType a) -> [v]
  (prf, eqt@(EqualityType s _eq _l t v _v')) -> [unArg v, prf]


-- | Compute the clauses for the with-function given the original patterns.
buildWithFunction
  :: [Name]               -- ^ Names of the module parameters of the parent function.
  -> QName                -- ^ Name of the parent function.
  -> QName                -- ^ Name of the with-function.
  -> Type                 -- ^ Types of the parent function.
  -> [NamedArg DeBruijnPattern] -- ^ Parent patterns.
  -> Nat                  -- ^ Number of module parameters in parent patterns
  -> Substitution         -- ^ Substitution from parent lhs to with function lhs
  -> Permutation          -- ^ Final permutation.
  -> Nat                  -- ^ Number of needed vars.
  -> Nat                  -- ^ Number of with expressions.
  -> [A.SpineClause]      -- ^ With-clauses.
  -> TCM [A.SpineClause]  -- ^ With-clauses flattened wrt. parent patterns.
buildWithFunction cxtNames f aux t qs npars withSub perm n1 n cs = mapM buildWithClause cs
  where
    -- Nested with-functions will iterate this function once for each parent clause.
    buildWithClause (A.Clause (A.SpineLHS i _ ps wps) inheritedDots rhs wh catchall) = do
      let (wps0, wps1) = genericSplitAt n wps
          ps0          = map defaultNamedArg wps0
      reportSDoc "tc.with" 50 $ text "inheritedDots:" <+> vcat [ prettyTCM x <+> text "=" <+> prettyTCM v <+> text ":" <+> prettyTCM a
                                                               | A.NamedDot x v a <- inheritedDots ]
      rhs <- buildRHS rhs
      (namedDots, ps') <- stripWithClausePatterns cxtNames f aux t qs npars perm ps
      let (ps1, ps2) = genericSplitAt n1 ps'
      let result = A.Clause (A.SpineLHS i aux (ps1 ++ ps0 ++ ps2) wps1) (inheritedDots ++ namedDots) rhs wh catchall
      reportSDoc "tc.with" 20 $ vcat
        [ text "buildWithClause returns" <+> prettyA result
        ]
      return result

    buildRHS rhs@A.RHS{}                 = return rhs
    buildRHS rhs@A.AbsurdRHS             = return rhs
    buildRHS (A.WithRHS q es cs)         = A.WithRHS q es <$>
      mapM ((A.spineToLhs . permuteNamedDots) <.> buildWithClause . A.lhsToSpine) cs
    buildRHS (A.RewriteRHS qes rhs wh) = flip (A.RewriteRHS qes) wh <$> buildRHS rhs

    -- The named dot patterns computed by buildWithClause lives in the context
    -- of the top with-clause (of the current call to buildWithFunction). When
    -- we recurse we expect inherited named dot patterns to live in the context
    -- of the innermost parent clause.
    permuteNamedDots (A.Clause lhs dots rhs wh catchall) =
      A.Clause lhs (applySubst withSub dots) rhs wh catchall

{-| @stripWithClausePatterns cxtNames parent f t qs np π ps = ps'@

[@Δ@]   context bound by lhs of original function (not an argument).

[@f@]   name of @with@-function.

[@t@]   type of the original function.

[@qs@]  internal patterns for original function.

[@np@]  number of module parameters in @qs@

[@π@]   permutation taking @vars(qs)@ to @support(Δ)@.

[@ps@]  patterns in with clause (eliminating type @t@).

[@ps'@] patterns for with function (presumably of type @Δ@).

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
~force (test (suc n , as) t p) | b , bs = {!!}
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

Note: stripWithClausePatterns factors @ps@ through @qs@, thus

@
  ps = qs[ps']
@

where @[..]@ is to be understood as substitution.
The projection patterns have vanished from @ps'@ (as they are already in @qs@).
-}

stripWithClausePatterns
  :: [Name]                   -- ^ Names of the module parameters of the parent function
  -> QName                    -- ^ Name of the parent function.
  -> QName                    -- ^ Name of with-function.
  -> Type                     -- ^ __@t@__   type of the original function.
  -> [NamedArg DeBruijnPattern] -- ^ __@qs@__  internal patterns for original function.
  -> Nat                      -- ^ __@npars@__ number of module parameters is @qs@.
  -> Permutation              -- ^ __@π@__   permutation taking @vars(qs)@ to @support(Δ)@.
  -> [NamedArg A.Pattern]     -- ^ __@ps@__  patterns in with clause (eliminating type @t@).
  -> TCM ([A.NamedDotPattern], [NamedArg A.Pattern]) -- ^ __@ps'@__ patterns for with function (presumably of type @Δ@).
stripWithClausePatterns cxtNames parent f t qs npars perm ps = do
  -- Andreas, 2014-03-05 expand away pattern synoyms (issue 1074)
  ps <- expandPatternSynonyms ps
  psi <- insertImplicitPatternsT ExpandLast ps t
  reportSDoc "tc.with.strip" 10 $ vcat
    [ text "stripping patterns"
    , nest 2 $ text "t   = " <+> prettyTCM t
    , nest 2 $ text "psi = " <+> fsep (punctuate comma $ map prettyA psi)
    , nest 2 $ text "qs  = " <+> fsep (punctuate comma $ map (prettyTCM . namedArg) qs)
    , nest 2 $ text "perm= " <+> text (show perm)
    ]
  -- Andreas, 2015-11-09 Issue 1710: self starts with parent-function, not with-function!
  (ps', namedDots) <- runWriterT $ strip (Def parent []) t psi $ drop npars qs
  reportSDoc "tc.with.strip" 50 $ nest 2 $
    text "namedDots:" <+> vcat [ prettyTCM x <+> text "=" <+> prettyTCM v <+> text ":" <+> prettyTCM a | A.NamedDot x v a <- namedDots ]
      -- We need to add the patterns for the module parameters before
      -- permuting.
  let paramPat i (VarP x) = A.VarP (cxtNames !! i)
      paramPat _ (DotP _) = A.WildP patNoRange
      paramPat _ _ = __IMPOSSIBLE__
  let psp = permute perm $ zipWith (fmap . fmap . paramPat) [0..] (take npars qs) ++ ps'
  reportSDoc "tc.with.strip" 10 $ vcat
    [ nest 2 $ text "ps' = " <+> fsep (punctuate comma $ map prettyA ps')
    , nest 2 $ text "psp = " <+> fsep (punctuate comma $ map prettyA $ psp)
    ]
  -- Andreas, 2014-03-05 Issue 142:
  -- In some cases, permute throws away some dot patterns of ps'
  -- which are then never checked.
  if True then return (namedDots, psp) else do
    -- Andreas, 2014-03-05 Disabled the fix for issue 142, the following is dead code:
    forM_ (permute (droppedP perm) ps') $ \ p -> setCurrentRange p $ do
      reportSDoc "tc.with.strip" 10 $ text "warning: dropped pattern " <+> prettyA p
      reportSDoc "tc.with.strip" 60 $ text $ show p
      case namedArg p of
        A.DotP info e -> case unScope e of
          A.Underscore{} -> return ()
          -- Dot patterns without a range are Agda-generated from a user dot pattern
          -- so we only complain if there is a range.
          e | getRange info /= noRange -> typeError $ GenericError $
            "This inaccessible pattern is never checked, so only _ allowed here"
          _ -> return ()
        _ -> return ()
    return (namedDots, psp)
  where

    strip
      :: Term                         -- ^ Self.
      -> Type                         -- ^ The type to be eliminated.
      -> [NamedArg A.Pattern]       -- ^ With-clause patterns.
      -> [NamedArg DeBruijnPattern] -- ^ Parent-clause patterns with de Bruijn indices relative to Δ.
      -> WriterT [A.NamedDotPattern] TCM [NamedArg A.Pattern]
            -- ^ With-clause patterns decomposed by parent-clause patterns.
            --   Also outputs named dot patterns from the parent clause that
            --   we need to add let-bindings for.

    -- Case: out of with-clause patterns.
    strip self t [] qs@(_ : _) = do
      reportSDoc "tc.with.strip" 15 $ vcat
        [ text "strip (out of A.Patterns)"
        , nest 2 $ text "qs  =" <+> fsep (punctuate comma $ map (prettyTCM . namedArg) qs)
        , nest 2 $ text "self=" <+> prettyTCM self
        , nest 2 $ text "t   =" <+> prettyTCM t
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
          implicit (A.ConP ci _ _) = patOrigin ci == ConPImplicit
          implicit _               = False
      unless (all (implicit . namedArg) ps) $
        typeError $ GenericError $ "Too many arguments given in with-clause"
      return []

    -- Case: both parent-clause pattern and with-clause pattern present.
    -- Make sure they match, and decompose into subpatterns.
    strip self t ps0@(p0 : ps) qs0@(q : qs) = do
      p <- liftTCM $ expandLitPattern p0
      reportSDoc "tc.with.strip" 15 $ vcat
        [ text "strip"
        , nest 2 $ text "ps0 =" <+> fsep (punctuate comma $ map prettyA ps0)
        , nest 2 $ text "exp =" <+> prettyA p
        , nest 2 $ text "qs0 =" <+> fsep (punctuate comma $ map (prettyTCM . namedArg) qs0)
        , nest 2 $ text "self=" <+> prettyTCM self
        , nest 2 $ text "t   =" <+> prettyTCM t
        ]
      let failDotPat :: Monoid w => WriterT w TCM a
          failDotPat = do
            d <- liftTCM $ prettyA p
            typeError $ GenericError $
                "Inaccessible (dotted) patterns from the parent clause must " ++
                "also be inaccessible in the with clause, when checking the " ++
                "pattern " ++ show d ++ ","
      case namedArg q of
        ProjP o d -> case A.maybePostfixProjP p of
          Just (o', AmbQ ds) -> do
            let d' = head ds
            when (length ds /= 1) __IMPOSSIBLE__
            d' <- liftTCM $ getOriginalProjection d'
            -- We assume here that neither @o@ nor @o'@ can be @ProjSystem@.
            if o /= o' then liftTCM $ mismatchOrigin o o' else do
            if d /= d' then mismatch else do
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

        VarP x  -> do
          ps <- intro1 t $ \ t -> strip (self `apply1` var (dbPatVarIndex x)) t ps qs
          return $ p : ps

        DotP v  -> case namedArg p of
          A.DotP _ _    -> ok p
          A.WildP _     -> ok p
          -- Ulf, 2016-05-30: dot patterns are no longer mandatory so a parent
          -- dot pattern can appear as a variable in the child clause. Indeed
          -- this happens if you use a variable in the parent and '...' in the
          -- child. In this case we need to remember the the binding, so we can
          -- insert a let for it.
          A.VarP x -> do
            (a, _) <- mustBePi t
            tell [A.NamedDot x v (unDom a)]
            ok p
          -- Andreas, 2013-03-21 in case the implicit A.pattern has already been eta-expanded
          -- we just fold it back.  This fixes issues 665 and 824.
          A.ConP ci _ _ | patOrigin ci == ConPImplicit -> okFlex p
          -- Andreas, 2015-07-07 issue 1606: Same for flexible record patterns.
          -- Agda might have replaced a record of dot patterns (A.ConP) by a dot pattern (I.DotP).
          p'@A.ConP{} -> ifM (liftTCM $ isFlexiblePattern p') (okFlex p) {-else-} failDotPat

          p@(A.PatternSynP pi' c' [ps']) -> do
             reportSDoc "impossible" 10 $
               text "stripWithClausePatterns: encountered pattern synonym " <+> prettyA p
             __IMPOSSIBLE__

          _ -> failDotPat
          where
            okFlex = ok . makeImplicitP
            ok p = do
              t' <- piApply1 t v
              (p :) <$> strip (self `apply1` v) t' ps qs

        q'@(ConP c ci qs') -> do
         reportSDoc "tc.with.strip" 60 $
           text "parent pattern is constructor " <+> prettyTCM c
         (a, b) <- mustBePi t
         -- The type of the current pattern is a datatype.
         Def d es <- liftTCM $ ignoreSharing <$> normalise (unEl $ unDom a)
         let us = fromMaybe __IMPOSSIBLE__ $ allApplyElims es
         -- Get the original constructor and field names.
         c <- (`withRangeOf` c) <$> do liftTCM $ getConForm $ conName c

         case namedArg p of

          -- Andreas, 2015-07-07 Issue 1606.
          -- Agda sometimes changes a record of dot patterns into a dot pattern,
          -- so the user should be allowed to do likewise.
          A.DotP{} -> ifNotM (liftTCM $ isFlexiblePattern q') mismatch $ {-else-} do
            maybe __IMPOSSIBLE__ (\ p -> strip self t (p : ps) qs0) =<< do
              liftTCM $ expandImplicitPattern' (unDom a) $ makeImplicitP p

          -- Andreas, 2013-03-21 if we encounter an implicit pattern
          -- in the with-clause, we expand it and restart
          -- Andreas, 2015-07-07 Issue 1606 do this whenever the parent
          -- is a record pattern, regardless of whether it came from an implicit
          -- or not.  This allows to drop hidden flexible record patterns from
          -- the with clauses even when they were present in the parent clause.
          A.WildP{} | Just _ <- conPRecord ci -> do
            maybe __IMPOSSIBLE__ (\ p -> strip self t (p : ps) qs0) =<< do
              liftTCM $ expandImplicitPattern' (unDom a) p

          A.ConP _ (A.AmbQ cs') ps' -> do
            -- Check whether the with-clause constructor can be (possibly trivially)
            -- disambiguated to be equal to the parent-clause constructor.
            cs' <- liftTCM $ mapM getConForm cs'
            unless (elem c cs') mismatch
            -- Strip the subpatterns ps' and then continue.
            stripConP d us b c qs' ps'

          A.RecP _ fs -> caseMaybeM (liftTCM $ isRecord d) mismatch $ \ def -> do
            ps' <- liftTCM $ insertMissingFields d (const $ A.WildP empty) fs (recordFieldNames def)
            stripConP d us b c qs' ps'

          p@(A.PatternSynP pi' c' ps') -> do
             reportSDoc "impossible" 10 $
               text "stripWithClausePatterns: encountered pattern synonym " <+> prettyA p
             __IMPOSSIBLE__

          p -> do
           reportSDoc "tc.with.strip" 60 $
             text $ "with clause pattern is  " ++ show p
           mismatch

        LitP lit -> case namedArg p of
          A.LitP lit' | lit == lit' -> do
            (a, b) <- mustBePi t
            let v = Lit lit
            strip (self `apply1` v) (b `absApp` v) ps qs

          p@(A.PatternSynP pi' c' [ps']) -> do
             reportSDoc "impossible" 10 $
               text "stripWithClausePatterns: encountered pattern synonym " <+> prettyA p
             __IMPOSSIBLE__

          _ -> mismatch
      where
        mismatch = typeError $
          WithClausePatternMismatch (namedArg p0) (dbPatVarName <$> namedArg q)
        mismatchOrigin o o' = typeError . GenericDocError =<< fsep
          [ text "With clause pattern"
          , prettyA p0
          , text "is not an instance of its parent pattern"
          , prettyTCM $ dbPatVarName <$> namedArg q
          , text $ "since the parent pattern is " ++ prettyProjOrigin o ++
                   " and the with clause pattern is " ++ prettyProjOrigin o'
          ]
        prettyProjOrigin ProjPrefix  = "a prefix projection"
        prettyProjOrigin ProjPostfix = "a postfix projection"
        prettyProjOrigin ProjSystem  = __IMPOSSIBLE__

        -- | Make an ImplicitP, keeping arg. info.
        makeImplicitP :: NamedArg A.Pattern -> NamedArg A.Pattern
        makeImplicitP = updateNamedArg $ const $ A.WildP patNoRange

        -- case I.ConP / A.ConP
        stripConP
          :: QName
             -- ^ Data type name of this constructor pattern.
          -> [Arg Term]
             -- ^ Data type arguments of this constructor pattern.
          -> Abs Type
             -- ^ Type the remaining patterns eliminate.
          -> ConHead
             -- ^ Constructor of this pattern.
          -> [NamedArg DeBruijnPattern]
             -- ^ Argument patterns (parent clause).
          -> [NamedArg A.Pattern]
             -- ^ Argument patterns (with clause).
          -> WriterT [A.NamedDotPattern] TCM [NamedArg A.Pattern]
             -- ^ Stripped patterns.
        stripConP d us b c qs' ps' = do

          -- Get the type and number of parameters of the constructor.
          Defn {defType = ct, theDef = Constructor{conPars = np}}  <- getConInfo c
          -- Compute the argument telescope for the constructor
          let ct' = ct `piApply` genericTake np us
          TelV tel' _ <- liftTCM $ telView ct'

          reportSDoc "tc.with.strip" 20 $
            vcat [ text "ct  = " <+> prettyTCM ct
                 , text "ct' = " <+> prettyTCM ct'
                 , text "np  = " <+> text (show np)
                 , text "us  = " <+> prettyList (map prettyTCM us)
                 , text "us' = " <+> prettyList (map prettyTCM $ genericTake np us)
                 ]

          -- Compute the new type
          let v     = Con c [ Arg info (var i) | (i, Arg info _) <- zip (downFrom $ size qs') qs' ]
              t' = tel' `abstract` absApp (raise (size tel') b) v
              self' = tel' `abstract` apply1 (raise (size tel') self) v  -- Issue 1546

          reportSDoc "tc.with.strip" 15 $ sep
            [ text "inserting implicit"
            , nest 2 $ prettyList $ map prettyA (ps' ++ ps)
            , nest 2 $ text ":" <+> prettyTCM t'
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
  :: QName                -- ^ The name of parent function.
  -> QName                -- ^ The name of the @with@-function.
  -> Telescope            -- ^ __@Δ₁@__      The arguments of the @with@ function before the @with@ expressions.
  -> Telescope            -- ^ __@Δ₂@__      The arguments of the @with@ function after the @with@ expressions.
  -> Nat                  -- ^ __@n@__       The number of @with@ expressions.
  -> [NamedArg DeBruijnPattern]   -- ^ __@qs@__      The parent patterns.
  -> Permutation          -- ^ __@perm@__    Permutation to split into needed and unneeded vars.
  -> Permutation          -- ^ __@lhsPerm@__ Permutation reordering the variables in parent patterns.
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
  let display = Display arity (replicate arity $ Apply $ defaultArg $ var 0) dt

  -- Debug printing.
  let addFullCtx = addContext delta1
                 . flip (foldr addContext) (for [1..n] $ \ i -> "w" ++ show i)
                 . addContext delta2
  reportSDoc "tc.with.display" 20 $ vcat
    [ text "withDisplayForm"
    , nest 2 $ vcat
      [ text "f      =" <+> text (show f)
      , text "aux    =" <+> text (show aux)
      , text "delta1 =" <+> prettyTCM delta1
      , text "delta2 =" <+> do addContext delta1 $ prettyTCM delta2
      , text "n      =" <+> text (show n)
      , text "perm   =" <+> text (show perm)
      , text "top    =" <+> do addFullCtx $ prettyTCM topArgs
      , text "qs     =" <+> sep (map (prettyTCM . namedArg) qs)
      , text "qsToTm =" <+> prettyTCM tqs0 -- ctx would be permuted form of delta1 ++ delta2
      , text "ys     =" <+> text (show ys)
      , text "rho    =" <+> text (prettyShow rho)
      , text "qs[rho]=" <+> do addFullCtx $ prettyTCM tqs
      , text "dt     =" <+> do addFullCtx $ prettyTCM dt
      ]
    ]
  reportSDoc "tc.with.display" 70 $ nest 2 $ vcat
      [ text "raw    =" <+> text (show display)
      ]

  return display
  where
    -- Ulf, 2014-02-19: We need to rename the module parameters as well! (issue1035)
    -- sub top ys wild = map term [0 .. m - 1] ++# raiseS (length qs)
    -- Andreas, 2015-10-28: Yes, but properly! (Issue 1407)
    sub top ys wild = parallelS $ map term [0 .. m + top - 1]
      where
        term i = maybe wild var $ findIndex (Just i ==) ys
    -- -- OLD
    -- sub top rho wild = parallelS $ map term [0 .. m - 1] ++ topTerms
    --   where
    --     -- Ulf, 2014-02-19: We need to rename the module parameters as well! (issue1035)
    --     newVars  = length qs
    --     topTerms = [ var (i + newVars) | i <- [0..top - 1] ]
    --     -- thinking required.. but ignored
    --     -- dropping the reverse seems to work better
    --     -- Andreas, 2010-09-09: I DISAGREE.
    --     -- Ulf, 2011-09-02: Thinking done. Neither was correct.
    --     -- We had the wrong permutation and we used it incorrectly. Should work now.
    --     term i = maybe wild var $ findIndex (Just i ==) rho

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
    toTerm p = case p of
      ProjP _ d   -> DDef d [] -- WRONG. TODO: convert spine to non-spine ... DDef d . defaultArg
      VarP x      -> DTerm  $ var $ dbPatVarIndex x
      DotP t      -> DDot   $ t
      ConP c _ ps -> DCon c $ toTerms ps
      LitP l      -> DTerm  $ Lit l
