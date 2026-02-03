-- | Implementation of conversion checking errors which can reify part
-- of the context leading to the actual failure as terms.
module Agda.TypeChecking.Conversion.Errors
  (
  -- * Public interface
  -- $convErrors
    failConversion, mismatchedProjections, addConversionContext,

  -- * Unreifiable recursive calls
  -- $stackSlice
    nowConversionChecking, cutConversionErrors

  -- * Types
  , ConversionError(..)
  , ConversionZipper(..)
  , ConversionErrorContext(..)
  , FailedCompareAs(..)
  )
  where

import Control.Monad.Error.Class
import Control.Monad.Trans.Maybe
import Control.Monad.Except
import Control.Applicative
import Control.DeepSeq
import Control.Monad

import GHC.Generics (Generic)

import qualified Agda.Syntax.Common.Pretty as P
import Agda.Syntax.Internal
import Agda.Syntax.Fixity (Precedence(TopCtx))
import Agda.Syntax.Common

import Agda.TypeChecking.Monad.Constraints
import Agda.TypeChecking.Monad.Statistics
import Agda.TypeChecking.Monad.SizedTypes
import Agda.TypeChecking.Monad.Signature
import Agda.TypeChecking.Monad.MetaVars
import Agda.TypeChecking.Monad.Builtin
import Agda.TypeChecking.Monad.Closure
import Agda.TypeChecking.Monad.Context
import Agda.TypeChecking.Monad.Debug
import Agda.TypeChecking.Monad.Pure
import Agda.TypeChecking.Monad.Base

import {-# SOURCE #-} Agda.TypeChecking.Errors
import Agda.TypeChecking.Conversion.Pure
import Agda.TypeChecking.Substitute
import Agda.TypeChecking.Telescope
import Agda.TypeChecking.Warnings
import Agda.TypeChecking.Records
import Agda.TypeChecking.Pretty
import Agda.TypeChecking.Reduce

import qualified Agda.Utils.Null as Null
import Agda.Utils.Impossible
import Agda.Utils.Functor
import Agda.Utils.Maybe
import Agda.Utils.Monad hiding (guard)
import Agda.Utils.Size

-- | The failing version of 'CompareAs'.
data FailedCompareAs
  = FailAsTermsOf Type Type
    -- ^ The conversion checker failed in a typed context.
    --
    -- While the conversion checker is homogeneous (so 'AsTermsOf' only
    -- stores a single type), a failing argument comparison early in the
    -- spine of a dependent function can cause the reconstructed
    -- "context" terms to be heterogeneous.
  | FailAsTypes
    -- ^ The conversion checker failed in a type-insensitive context.
  deriving (Show, Generic)

-- | A "zipper-like" representation of the edges between comparing a
-- normal form and comparing one of its immediate subterms in the
-- conversion checker's call graph.
data ConversionZipper
  -- | Thrown at the failing call.
  = ConvStop

  -- | A call to compare the body of a function-typed value.
  | ConvLam
      (Dom Type)       -- ^ Argument type
      (Abs ())         -- ^ Simplified codomain
      ArgName          -- ^ Name of the variable introduced for comparing the bodies
      ConversionZipper -- ^ Call stack suffix.

  -- | A call to compare the domain of a pair of pi types.
  | ConvDom
      (Dom ConversionZipper) -- ^ Information about the domain, and call stack suffix.
      (Abs Type)             -- ^ Codomain of the left-hand side type.
      (Abs Type)             -- ^ Codomain of the right-hand-side type.

  -- | A call to compare the codomain of a pair of pi types.
  | ConvCod
      (Dom Type)             -- ^ The domain.
      ArgName                -- ^ Name of the variable introduced for comparing the bodies
      ConversionZipper       -- ^ Call stack suffix.

  -- | A call to compare an argument to a function.
  | ConvApply
      Term                    -- ^ The head term
      (Abs Type)              -- ^ The codomain of the function type at the argument where conversion failed
      (Arg ConversionZipper)  -- ^ Information about the argument, and call stack suffix.
      [Elim]                  -- ^ Remaining arguments from the LHS term that conversion checking could not get to.
      [Elim]                  -- ^ Remaining arguments from the RHS term that conversion checking could not get to.
  deriving (Show, Generic)

-- | Additional information regarding why two function types are distinct.
data WhyUnequalTypes
  = forall a. (NFData a, Verbalize a) => UnequalDomain a a
    -- ^ Their domains differ in relevance/modality/etc.
  | UnequalHiding Hiding Hiding
    -- ^ Their domains differ in hiding.

-- | Additional information as for why two terms which might print the
-- same are distinct.
--
-- Some constructors are duplicated so that the explanations can be
-- printed in the correct order.
data HeadMismatch
  -- | They are distinct extended lambdas.
  = HdmExtLam   QName QName
  -- | They are distinct 'Pi' types.
  | HdmTypes    WhyUnequalTypes
  -- | They are distinct variables.
  | HdmVars     Int   Int
  -- | They are the same variable, but their spines might be
  -- interesting.
  | HdmVarSpine Int (Closure (Elims, Elims))

  | HdmVarDef -- ^ Variable-definition mismatch
  | HdmDefVar -- ^ Definition-variable mismatch
  | HdmVarCon -- ^ Variable-constructor mismatch
  | HdmConVar -- ^ Constructor-variable mismatch
  deriving (Show, Generic)

-- | Whether a 'ConversionZipper' generated nontrivial wrapper terms
-- when flattening the call stack of a t'ConversionError'.
--
-- Used to print error messages with correct grammar.
data HereOrThere
  = Here  -- ^ It didn't.
  | There -- ^ It did.
  deriving (Show, Generic)

-- | Context for a conversion checking error.
data ConversionErrorContext
  = Floating ConversionZipper
    -- ^ It still makes sense to collect call stack information for this
    -- error.
  | Finished HereOrThere (Maybe HeadMismatch)
    -- ^ We can not, or do not want to, keep collecting call stack
    -- information for this error.
    -- Stores "crystallised" information about the actual failing
    -- comparison to use as context in error rendering.
  deriving (Show, Generic)

-- | A conversion checking failure.
--
-- A conversion checking error can be in two states (according to its
-- 'convErrCtx'): it is either 'Finished' or
-- 'Agda.TypeChecking.Conversion.Errors.Floating'.
--
-- A 'Finished' conversion-checking error packages a pair of unequal
-- terms, which are well-typed in the context that the error was raised
-- in, with sufficient information for printing an informative error
-- message. 'Finished' errors will not accumulate further call stack
-- information.
--
-- A 'Agda.TypeChecking.Conversion.Errors.Floating' conversion-checking
-- error is subject to be modified as the conversion checker's call
-- stack unwinds, by appending to its 'ConversionZipper'. Some frames in
-- a 'ConversionZipper' alter the context in which the terms
-- 'convErrLhs' and 'convErrRhs' should be interpreted. Floating errors
-- can be re-raised as 'Finished' errors using 'cutConversionErrors'.
-- This means that any code which catches those errors will have types
-- valid directly in the v'TypeError' closure, but no more context will
-- be accumulated for them.
data ConversionError = ConversionError
  { convErrCmp   :: Comparison
    -- ^ Were we checking for equality or subtyping?
  , convErrTys   :: FailedCompareAs
    -- ^ Were we comparing against a known type when conversion checking
    -- failed?
  , convErrLhs   :: Term
    -- ^ The "LHS" of the comparison (if 'CmpLeq', the subtype).
  , convErrRhs   :: Term
    -- ^ The "RHS" of the comparison (if 'CmpLeq', the supertype).
  , convErrCtx   :: ConversionErrorContext
    -- ^ Call stack information about this error.
  }
  deriving (Show, Generic)

instance Show WhyUnequalTypes where
  show = const "<WhyUnequalTypes>"

instance NFData WhyUnequalTypes where
  rnf = \case
    UnequalDomain     a b -> rnf (a, b)
    UnequalHiding     a b -> rnf (a, b)

instance NFData ConversionErrorContext
instance NFData ConversionZipper
instance NFData ConversionError
instance NFData FailedCompareAs
instance NFData HeadMismatch
instance NFData HereOrThere

-- $convErrors
--
-- Conversion checking errors are initially thrown (by 'failConversion')
-- in the /floating/ state, which means they can accumulate information
-- on where they happened as the call stack unwinds. This information
-- will be presented to the user by wrapping the actual mismatched terms
-- in a skeleton of the term where the mismatch happened. These terms
-- had better not be nonsense! This requires that recursive calls within
-- the conversion checker cooperate with the reconstruction process,
-- using the functions in this module. Their use can be summarised as
-- follows:
--
-- * A recursive call to compare a subterm of a normal form should be
--   guarded by 'addConversionContext'.
-- * A recursive call to a domain-specific conversion checking function
--   which takes the input terms apart using a nontrivial view (e.g.,
--   'Agda.TypeChecking.Conversion.equalLevel') should be guarded by
--   'nowConversionChecking'.
-- * A recursive call under an application of a nontrivial substitution
--   to the context and terms under consideration should be guarded by
--   'cutConversionErrors'.
-- * Recursive calls that preserve the definitional identities of the
--   terms under consideration do not need any special handling.
--
-- The goal of these rules is to allow for the user to pretend that
-- conversion checking works by normalising then checking for syntactic
-- equality: the reconstructed term should wrap the actual mismatch in
-- "hereditary neutrals (to the left)", i.e. everything that compared
-- equal on the way to the mismatched terms is normalised, but parts of
-- the term that are beyond the mismatch are left as-is (and, in the
-- future, will be presented "deemphasized").
--
-- /How much/ of the context to reify is a design parameter that can be
-- tuned. At the moment, we drop all 'ConvLam', 'ConvDom', 'ConvCod' and
-- __visible__ 'ConvApply' from the front of the zipper. Regardless, the
-- conversion checker must be set up as if the entire context will be
-- reified.

-- | Throw a floating t'ConversionError', given the arguments of
-- 'Agda.TypeChecking.Conversion.compareAs'.
failConversion
  :: (MonadTCError m, HasBuiltins m)
  => Comparison -- ^ Equality or subtyping?
  -> Term       -- ^ See 'convErrLhs'
  -> Term       -- ^ See 'convErrRhs'
  -> CompareAs  -- ^ Will be converted to a 'FailedCompareAs'.
  -> m a
failConversion cmp l r cas = do
  as <- case cas of
    AsTypes     -> pure FailAsTypes
    AsTermsOf t -> pure $ FailAsTermsOf t t
    AsSizes     -> do
      t <- sizeType
      pure $ FailAsTermsOf t t

  typeError $ ConversionError_ ConversionError
    { convErrTys = as
    , convErrRhs = r
    , convErrLhs = l
    , convErrCmp = cmp
    , convErrCtx = Floating ConvStop
    }

-- | Add some call stack context to floating t'ConversionError's thrown
-- from the continuation.
--
-- This function should be placed on the __outside__ of 'addContext',
-- and the changes to the context should be reflected in the
-- 'ConversionZipper'.
addConversionContext
  :: (MonadTCError m)
  => (ConversionZipper -> ConversionZipper)
    -- ^ How to modify the zipper
  -> m a
    -- ^ Generally, a recursive call to the conversion checker
  -> m a
addConversionContext ext cont = cont `catchError` \case
  TypeError loc st cl'@Closure{ clValue = ConversionError_ conv@ConversionError{ convErrCtx = Floating ctx } } -> do
    let
      zip   = ext ctx
      old_c = envCall (clEnv cl')
    cl <- buildClosure $ ConversionError_ $! conv { convErrCtx = Floating zip }
    zip `seq` old_c `seq` throwError $ TypeError loc st cl
      { clEnv = (clEnv cl) { envCall = old_c }
      }
  err -> throwError err

-- $stackSlice
--
-- The 'ConversionZipper' reflects recursive calls made to conversion
-- checking of the immediate subterms of a normal form, and it can
-- handle most cases of a recursive call happening in a weakening of the
-- current context as well. However, some conversion-checking functions
-- take the input values apart in nontrivial, type-specific ways before
-- eventually calling into "ordinary" term conversion checking again.
--
-- If a floating t'ConversionError' happens in one of these eventual
-- calls, the reified call stack will not have anything corresponding to
-- the value that got taken apart; this can result in the terms
-- presented to the user being ill-typed (see
-- @test/Fail/ConvErrCtxLevels@ for an example). These calls can be
-- handled in two ways, depending on whether or not preserving the
-- surrounding context is likely to be useful in an error message. Here
-- are examples of using each:
--
-- *
--     Calls to 'Agda.TypeChecking.Conversion.equalLevel' are likely to
--     happen while checking hidden arguments to a defined symbol (e.g.
--     a universe-polymorphic data type), which is a context worth
--     preserving for error messages: telling the user @l != l'@ is
--     significantly less useful than telling them @List {l} A != List
--     {l'} B@.
--
--     Therefore, the call to 'Agda.TypeChecking.Conversion.equalLevel'
--     in 'Agda.TypeChecking.Conversion.equalTerm'' is guarded by
--     'nowConversionChecking'.  If an error happens while
--     conversion-checking some levels, the mismatched terms will be
--     /replaced/ by the (normalised forms of) the entire levels that
--     were being compared.
--
-- *
--     On the other hand, conversion checking of partial elements
--     involves nontrivial modifications to the context, and, more
--     importantly, generally happens to terms which display quite
--     terribly /before/ these substitutions are applied, often
--     involving eta-expanded extended lambdas and the primitive
--     @primPOr@. Subjectively, it's less useful to say that conversion
--     checking failed for the hard-to-read system than it is to say
--     that it failed for a particular face.
--
--     For these reasons,
--     'Agda.TypeChecking.Conversion.compareTermOnFace' (really,
--     'Agda.TypeChecking.Conversion.forallFaceMaps') uses
--     'cutConversionErrors' to turn any floating errors from
--     conversion-checking the faces into 'Finished' errors, which no
--     longer accumulate context. Whatever context was collected
--     /inside/ the face comparison will be preserved, but we will not
--     remember /that/ (or /where/) the partial elements were being
--     compared.

-- | Replaces any floating t'ConversionError's raised by the
-- continuation with the one generated (as per 'failConversion') from
-- the given arguments.
nowConversionChecking
  :: forall m a. (MonadTCError m, HasBuiltins m)
  => Comparison -- ^ Equality or subtyping?
  -> Term       -- ^ See 'convErrLhs'
  -> Term       -- ^ See 'convErrRhs'
  -> CompareAs  -- ^ Will be converted to a 'FailedCompareAs'.
  -> m a        -- ^ Generally, a recursive call to a type-specific conversion checking function.
  -> m a
nowConversionChecking cmp l r cas cont = cont `catchError` \case
  TypeError loc st Closure{ clValue = err }
    | ConversionError_ ConversionError{ convErrCtx = Floating{} } <- err
    -> failConversion cmp l r cas
  err -> throwError err

-- | Freeze t'ConversionError's thrown by the continuation.
--
-- This function should be placed on the __inside__ of context updates.
cutConversionErrors
  :: (MonadPretty m, MonadError TCErr m)
  => m a -> m a
cutConversionErrors cont = cont `catchError` \case
  TypeError loc st cl@Closure{ clValue = ConversionError_ conv } -> enterClosure cl \_ ->
    flattenConversionError conv \conv@ConversionError{convErrLhs = lhs, convErrRhs = rhs} -> do
      cl <- buildClosure ()
      throwError $ TypeError loc st $ cl $> case (lhs, rhs) of
        (Sort MetaS{} , t            ) -> ShouldBeASort $ El __IMPOSSIBLE__ t
        (s            , Sort MetaS{} ) -> ShouldBeASort $ El __IMPOSSIBLE__ s
        (Sort DefS{}  , t            ) -> ShouldBeASort $ El __IMPOSSIBLE__ t
        (s            , Sort DefS{}  ) -> ShouldBeASort $ El __IMPOSSIBLE__ s
        _                              -> ConversionError_ conv
  err -> throwError err

-- | Intermediate type for storing the results of flattening a 'ConversionZipper'.
type ConversionProblem = (FailedCompareAs, Term, Term)

-- | @'eliminateLhsRhs' hd1 ty1 es1 hd2 ty2 es2@ generates a
-- @ConversionProblem@ between the mismatched terms @hd1@ and @hd2@,
-- which have the types @ty1@ and @ty2@ respectively.
--
-- If the types @ty1@ and @ty2@ respond to the given eliminations @es1@
-- and @es2@ respectively (which they should, since the inputs to
-- conversion checking are assumed to be well-typed), the mismatched
-- terms accumulate these, and the types are suitably refined.
--
-- Currently replaces large terms in the @es1@ by 'DontCare', as a HACK
-- to avoid the printing of big uncompared terms. In the future, this is
-- probably better handled in the reifier.
eliminateLhsRhs
  :: forall m. PureTCM m
  => Type -> Term -> Elims
  -> Type -> Term -> Elims
  -> m ConversionProblem
eliminateLhsRhs t1 v1 l_es t2 v2 r_es =
  let
    blank t
      | termSize t >= 15 = DontCare t
      | otherwise        = t
  in
  fromMaybeT (FailAsTermsOf t1 t2, v1, v2) do
    t1 <- eliminateType mzero v1 t1 l_es
    t2 <- eliminateType mzero v2 t2 r_es
    pure
      ( FailAsTermsOf t1 t2
      , v1 `applyE` map (fmap blank) l_es
      , v2 `applyE` map (fmap blank) r_es
      )

-- | @'mismatchedProjections' t1 v1 e1 t2 v2 e2@ raises a floating
-- conversion-checking error (as per 'failConversion') indicating that
-- the terms @v1@ and @v2@ (which have type @t1@ and @t2@ respectively,
-- and are typically neutral) disagree on the last elimination in their
-- spines.
--
-- The further eliminations @e1@ and @e2@ are treated as "uncompared"
-- context for the error message.
mismatchedProjections
  :: (MonadError TCErr m, PureTCM m)
  => Type  -- ^ LHS type, @t1@
  -> Term  -- ^ LHS term, @v1@; see 'convErrLhs'.
  -> Elims -- ^ Additional eliminations @e1@ present on the LHS beyond the failure of conversion checking
  -> Type  -- ^ RHS type, @t2@
  -> Term  -- ^ RHS term, @v2@; see 'convErrRhs'.
  -> Elims -- ^ Additional eliminations @e2@ present on the RHS beyond the failure of conversion checking
  -> m a
mismatchedProjections t1 v1 e1 t2 v2 e2 = do
  (tys, lhs, rhs) <- eliminateLhsRhs t1 v1 e1 t2 v2 e2
  typeError $ ConversionError_ $ ConversionError CmpEq tys lhs rhs (Floating ConvStop)

-- | Compute a 'HeadMismatch' explaining why two terms disagree, if
-- there is a possibility that they might be printed identically.
headMismatch :: forall m. (PureTCM m, MonadPlus m) => Term -> Term -> m HeadMismatch
headMismatch Var{}      Def{}      = pure HdmVarDef
headMismatch Def{}      Var{}      = pure HdmDefVar
headMismatch Var{}      Con{}      = pure HdmVarCon
headMismatch Con{}      Var{}      = pure HdmConVar
headMismatch (Var i xs) (Var j ys)
  | i == j = HdmVarSpine i <$> buildClosure (xs, ys)
headMismatch (Pi d1 _)  (Pi d2 _) =
  let
    hint :: (a -> a -> b) -> (forall x y. Dom' x y -> a) -> (a -> a -> Bool) -> m b
    hint k g c = k (g d1) (g d2) <$ guard (not (c (g d1) (g d2)))
  in HdmTypes <$> asum
    [ hint UnequalDomain     getRelevance     sameRelevance
    , hint UnequalDomain     getQuantity      sameQuantity
    , hint UnequalDomain     getModalPolarity samePolarity
    , hint UnequalDomain     getCohesion      sameCohesion
    , hint UnequalHiding     getHiding        sameHiding
    ]
headMismatch (Def i _)  (Def j _)
  | isExtendedLambdaName i, isExtendedLambdaName j = pure $ HdmExtLam i j
headMismatch (Var i xs) (Var j ys) = pure $ HdmVars i j
headMismatch lhs        rhs        = do
  reportSDoc "tc.conv.ctx" 30 $ vcat
    [ "headMismatch no match"
    , "  lhs:" <+> prettyTCM lhs
    , "  rhs:" <+> prettyTCM rhs
    ]
  mzero

-- | Flatten a Floating conversion checking error into one that
-- presents interesting context around the failing terms.
--
-- The continuation is only invoked with 'Finished' t'ConversionError's.
flattenConversionError :: forall m z. PureTCM m => ConversionError -> (ConversionError -> m z) -> m z
flattenConversionError e@ConversionError{convErrCtx = Finished{}} cont = cont e
flattenConversionError (ConversionError cmp tys lhs rhs (Floating ctx)) cont =
  do
    reportSDoc "tc.conv.ctx" 30 $ vcat
      [ "unwinding conversion zipper:"
      , "  env:" <+> (prettyTCM =<< getContextTelescope)
      , "  tys:" <+> prettyTCM tys
      , "  lhs:" <+> prettyTCM lhs
      , "  rhs:" <+> prettyTCM rhs
      , "  zip:" <+> prettyTCM ctx
      ]
    let
      k ht hdm (tys, lhs, rhs) = do
        reportSDoc "tc.conv.ctx" 30 $ vcat
          [ "conversion zipper unwound:"
          , "  env:" <+> (prettyTCM =<< getContextTelescope)
          , "  tys:" <+> prettyTCM tys
          , "  lhs:" <+> prettyTCM lhs
          , "  rhs:" <+> prettyTCM rhs
          , "  hdm:" <+> text (show hdm)
          ]
        cont (ConversionError cmp tys lhs rhs (Finished ht hdm))
    seek k ctx
  where

  -- Actually apply the continuation. This is the innermost function in
  -- handling the ConversionProblem, so this is our opportunity to
  -- collect any headMismatch information that might get buried in
  -- backtrace terms.
  done :: forall z. (HereOrThere -> Maybe HeadMismatch -> ConversionProblem -> m z) -> m z
  done ok = do
    reportSDoc "tc.conv.ctx" 30 $ vcat
      [ "reached center of conversion zipper:"
      , "  env:" <+> (prettyTCM =<< getContextTelescope)
      , "  tys:" <+> prettyTCM tys
      , "  lhs:" <+> pretty lhs
      , "  rhs:" <+> pretty rhs
      ]
    hdm <- runMaybeT $ headMismatch lhs rhs
    ok Here hdm (tys, lhs, rhs)

  -- Discard an uninteresting prefix of call stack (anything that does
  -- not mention an implicit argument), moving any binders from the
  -- zipper to the context of the continuation.
  seek
    :: forall z.  (HereOrThere -> Maybe HeadMismatch -> ConversionProblem -> m z)
    -> ConversionZipper
    -> m z
  seek ok zip = case zip of
    ConvStop -> done ok
    ConvApply hd ty (Arg info rest) l_es r_es
      | visible info                                   -> seek ok rest
      | Con c o _ <- hd, IsRecord{} <- conDataRecord c -> seek ok rest
    ConvLam dom ty name rest -> addContext (name, dom) $ seek ok rest
    ConvCod dom name rest    -> addContext (name, dom) $ seek ok rest
    ConvDom dom c1 c2        -> seek ok (unDom dom)
    _ -> reify zip (ok Here) ok

  -- Actually reifies a 'ConversionZipper' as a term around the conversion
  -- problem.
  -- This function takes both a success continuation (with three
  -- arguments) and a failing continuation, in case we had to give up on
  -- building the context term.
  reify
    :: forall z. ConversionZipper
    -> (Maybe HeadMismatch -> ConversionProblem -> m z)
    -> (HereOrThere -> Maybe HeadMismatch -> ConversionProblem -> m z)
    -> m z
  reify ctx err ok = case ctx of
    -- Empty call stack, nothing to do
    ConvStop -> done ok

    -- Going under binders.
    --
    -- These both function in the same way, though the lambda case seems
    -- much bigger because it has to update the expected types.
    --
    -- On the failure continuation, since we're not building a term
    -- wrapper to add any variables that are referred to by the
    -- mismatched terms, we have to move the binders into the context.
    --
    -- On the success continuation, the term binder is added, and (if
    -- possible) the comparison is updated for accuracy.
    ConvCod dom name rest -> reify rest (\hdm prob -> addContext (name, dom) $ err hdm prob)
      \_ hdm (_, lhs, rhs) -> ok There hdm
        ( FailAsTypes
        , Pi dom (mkAbs name (El __DUMMY_SORT__ lhs))
        , Pi dom (mkAbs name (El __DUMMY_SORT__ rhs))
        )

    ConvLam dom ty name rest -> reify rest
      (\hdm prob -> addContext (name, dom) $ err hdm prob)
      \ht hdm (cmp, lhs, rhs) -> ok There hdm
        ( case cmp of
            -- Ideally it would be provably impossible for a 'ConvLam'
            -- to be on the stack after an untyped comparison, but I
            -- can't be sure that this is actually the case.
            --
            -- If it does happen, it's safer to print a stupid-looking
            -- error (the types λ x → ... and λ x → ... are not equal)
            -- than it is to print an error with dummy terms.
            --
            -- And if someone complains about the error being stupid, we
            -- hopefully get a test case to fix it with.
            FailAsTypes       -> FailAsTypes
            -- If we do have the expected types then we can just wrap
            -- them in Pi types.
            FailAsTermsOf a b -> FailAsTermsOf
              (El (piSort (unEl <$> dom) (getSort dom) (getSort a <$ ty)) (Pi dom (a <$ ty)))
              (El (piSort (unEl <$> dom) (getSort dom) (getSort b <$ ty)) (Pi dom (b <$ ty)))
        , Lam (domInfo dom) (mkAbs name lhs), Lam (domInfo dom) (mkAbs name rhs)
        )

    -- Entering the domain of a function type. Bolts the codomains onto
    -- the failing term. No context handling is needed.
    ConvDom dom c1 c2 -> reify (unDom dom) err \_ hdm (_, lhs, rhs) -> ok There hdm
      ( FailAsTypes
      , Pi (El __DUMMY_SORT__ lhs <$ dom) c1
      , Pi (El __DUMMY_SORT__ rhs <$ dom) c2
      )

    -- Entering an argument to a neutral.
    ConvApply hd ty (Arg info rest) l_es r_es -> reify rest err \_ hdm prob@(_, lhs', rhs') ->
      let info' = info { argInfoOrigin = ConversionFail } in case hd of

        -- If the argument is to an extended lambda, we give up on
        -- reifying this frame (and anything it would return to) since
        -- that generally makes the error messages *worse*.
        -- This is the purpose of passing the failing continuation
        -- around.
        Def nm as | isExtendedLambdaName nm -> do
          ~Function{ funExtLam = Just (ExtLamInfo m b sys) } <- theDef <$> getConstInfo nm
          bs <- lookupSection m
          reportSDoc "tc.conv.ctx" 30 $ vcat
            [ "conversion context has extended lambda" <+> pretty nm
            , "bs " <> parens (pretty (size bs)) <> colon <> " " <> pretty bs
            , "as " <> parens (pretty (size as)) <> colon <> " " <> pretty as
            ]
          err hdm prob

        -- Otherwise, we just build the function call. Note that the
        -- ArgInfo is updated so that the reifier will print the
        -- mismatched term in case it happens in an implicit argument.
        _ -> ok There hdm =<< eliminateLhsRhs
          (ty `absApp` lhs') (hd `apply` [Arg info' lhs']) l_es
          (ty `absApp` rhs') (hd `apply` [Arg info' rhs']) r_es

instance PrettyTCM FailedCompareAs where
  prettyTCM = \case
    FailAsTypes{}     -> "(as types)"
    FailAsTermsOf a b -> prettyTCM a <+> comma <+> prettyTCM b

instance PrettyTCM ConversionZipper where
  prettyTCM = \case
    ConvStop -> "<>"
    ConvLam dom ret nm rest -> vcat
      [ "lam"   <+> pretty nm <+> pretty dom
      , "ret: " <+> pretty ret
      , "rest:"
      , nest 2 (prettyTCM rest)
      ]
    ConvCod dom nm rest -> vcat
      [ "cod"   <+> pretty nm <+> pretty dom
      , "rest:"
      , nest 2 (prettyTCM rest)
      ]
    ConvDom dom t1 t2 -> vcat
      [ "dom:" <+> pretty (() <$ dom)
      , "t1: " <+> pretty t1
      , "t2: " <+> pretty t2
      , "rest:"
      , nest 2 (prettyTCM (unDom dom))
      ]
    ConvApply hd ty (Arg info rest) lhs rhs -> vcat
      [ "apply" <+> pretty hd
      , "ty:  " <+> pretty ty
      , "lhs: " <+> prettyTCM lhs
      , "rhs: " <+> prettyTCM rhs
      , "rest:"
      , nest 2 (prettyTCM rest)
      ]

instance PrettyTCM ConversionError where
  prettyTCM :: forall m. MonadPretty m => ConversionError -> m Doc
  prettyTCM err = flattenConversionError err \(ConversionError cmp tys lhs rhs ~(Finished ht hdm)) -> do
    (d1, d2, disamb) <- prettyInEqual ht hdm lhs rhs
    let
      disambs = nest 2 $ orEmpty (pure <$> disamb)
      what = hdm >>= \case
        HdmTypes x -> Just x
        _          -> Nothing
    case tys of
      FailAsTermsOf lhs_t rhs_t -> runBlocked (pureEqualType lhs_t rhs_t) >>= \case
        Right True -> vcat
          [ "The terms", nest 2 (pure d1)
          , "and",       nest 2 (pure d2)
          , "are not equal at type " <> prettyTCM lhs_t <> orEmpty (comma <+> "because:" <$ disamb)
          , disambs
          ]
        _ -> vcat
          [ "The terms", nest 2 (pure d1 <+> colon <+> prettyTCM lhs_t)
          , "and",       nest 2 (pure d2 <+> colon <+> prettyTCM rhs_t)
          , "are not equal" <> orEmpty (comma <+> "because:" <$ disamb)
          , disambs
          ]
      FailAsTypes | CmpEq <- cmp -> vcat
        [ "The" <+> case what of
            Just UnequalDomain{} -> "function types"
            Just UnequalHiding{} -> "function types"
            _ -> "types"
        , nest 2 (pure d1), "and", nest 2 (pure d2)
        , "are not equal" <> orEmpty (comma <+> "because:" <$ disamb)
        , disambs
        ]
      FailAsTypes | CmpLeq <- cmp -> vcat
        [ "The" <+> case what of
            Just UnequalDomain{} -> "function type"
            Just UnequalHiding{} -> "function type"
            _ -> "type"
        , nest 2 (pure d1), "is not a subtype of", nest 2 (pure d2)
        , orEmpty ("because:" <$ disamb)
        , disambs
        ]

-- | Pretty print a pair of distinct terms @t1@ and @t2@, producing a
-- disambiguator if the terms render the same with the ambient settings
-- but differently with display forms.
displayDisamb
  :: forall m. MonadPretty m
  => HereOrThere                         -- ^ For grammar
  -> Maybe (Int, Closure (Elims, Elims))
    -- ^ From a 'HeadMismatch', to indicate what projections' display
    -- forms caused the rerender (if any)
  -> Term -- ^ @t1@
  -> Term -- ^ @t2@
  -> m (Doc, Doc, Maybe Doc)
displayDisamb ht hdm t1 t2 = do
  d1 <- prettyTCMCtx TopCtx t1
  d2 <- prettyTCMCtx TopCtx t2
  let
    maybeProjs :: Elims -> Elims -> MaybeT m [m Doc]
    maybeProjs (Proj _ p:xs) (Proj _ p':ys) | p /= p' = do
      df  <- hasDisplayForms p
      df' <- hasDisplayForms p'
      case (df, df') of
        (True, False)  -> pure $ pwords "a display form for" <> [prettyTCM p, "has"]
        (False, True)  -> pure $ pwords "a display form for" <> [prettyTCM p', "has"]
        (True, True)   -> pure $ pwords "display forms for"  <> [prettyTCM p, "and", prettyTCM p', "have"]
        (False, False) -> mzero
    maybeProjs (_:xs) (_:ys) = maybeProjs xs ys
    maybeProjs _ _           = mzero

  (d1, d2,) <$> runMaybeT do
    guard (P.render d1 == P.render d2)
    reportSDoc "tc.error.conv" 30 $ vcat
      [ "terms rendered the same"
      , "  t1:" <+> pretty t1
      , "  d1:" <+> pure d1
      , "  t2:" <+> pretty t2
      , "  d2:" <+> pure d2
      ]

    (d1, d2) <- locallyTC eDisplayFormsEnabled (const False) do
      (,) <$> prettyTCMCtx TopCtx t1 <*> prettyTCMCtx TopCtx t2
    guard (P.render d1 /= P.render d2)

    whatdf <- case hdm of
      Just (_, cl) -> enterClosure cl (lift . runMaybeT . uncurry maybeProjs) <&>
        fromMaybe (pwords "display forms have")
      Nothing      -> pure $ pwords "display forms have"

    vcat
      [ fsep $ map lift whatdf <> pwords "caused" <> pwords case ht of
          Here  -> "them"
          There -> "the mismatched terms"
      , nest 2 (pure d1), "and", nest 2 (pure d2)
      , "to render the same"
      ]


-- | Print two terms that are supposedly unequal, additionally returning
-- an explanation (informed by the HeadMismatch) if they happened to
-- print to the same thing.
prettyInEqual
  :: MonadPretty m
  => HereOrThere        -- ^ For grammar
  -> Maybe HeadMismatch -- ^ Collected disambiguator information
  -> Term -> Term -> m (Doc, Doc, Maybe Doc)
prettyInEqual ht hdm t1 t2
  -- If we don't know why they differ, or the mismatched terms are
  -- headed by the same variable, we defer to 'displayDisamb' which is
  -- capable of rendering the term without display forms to fish for an
  -- improvement in printing.
  | Nothing                 <- hdm = displayDisamb ht Nothing t1 t2
  | Just (HdmVarSpine i cl) <- hdm = displayDisamb ht (Just (i, cl)) t1 t2

  -- If they're distinct function types, we don't have to bother
  -- rerendering.
  | Just (HdmTypes x)       <- hdm =
    let
      ecore = case x of
        UnequalDomain a b -> pwords "one has"
          <> [hlKeyword (text (verbalize a))]
          <> pwords "domain, while the other is"
          <> [hlKeyword (text (verbalize b)) <> "."]
        UnequalHiding a b -> pwords "one takes"
          <> [hlKeyword (text (verbalize (Indefinite a)))]
          <> pwords "argument, while the other takes"
          <> [hlKeyword (text (verbalize (Indefinite b))), "argument."]
      explain = case ht of
        Here  -> fsep ecore
        There -> fsep $ pwords "the mismatched terms are function types;" <> ecore
    in (,,) <$> prettyTCMCtx TopCtx t1 <*> prettyTCMCtx TopCtx t2 <*> (Just <$> explain)

-- If it's some other class of mismatch, a rerender would probably not
-- improve things.
prettyInEqual ht (Just hdm) t1 t2 = do
  d1 <- prettyTCMCtx TopCtx t1
  d2 <- prettyTCMCtx TopCtx t2
  (d1, d2,) <$> runMaybeT do
    guard (P.render d1 == P.render d2)
    let
      mm = case ht of
        Here  -> []
        There -> pwords "of the mismatched terms"
    case hdm of
      HdmExtLam a b -> vcat
        [ fsep $
          case ht of
            Here  -> pure "they"
            There -> pwords "the mismatched terms"
          <> pwords "are distinct extended lambdas; "
        , fwords "one is defined at"
        , "  " <+> pretty (nameBindingSite (qnameName a))
        , fwords "and the other at"
        , "  " <+> (pretty (nameBindingSite (qnameName b)) <> ",")
        , fwords "so they have different internal representations."
        ]

      HdmVarDef   -> fsep $ pwords "one" <> mm <> pwords "is a variable, the other a definition"
      HdmVarCon   -> fsep $ pwords "one" <> mm <> pwords "is a variable, the other a constructor"
      HdmDefVar   -> fsep $ pwords "one" <> mm <> pwords "is a definition, the other a variable"
      HdmConVar   -> fsep $ pwords "one" <> mm <> pwords "is a constructor, the other a variable"
      HdmVars i j -> fsep $
           pwords "one" <> mm <> pwords "has de Bruijn index "
        <> [pretty i <> comma] <> pwords "the other" <> [pretty j]
