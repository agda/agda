module Agda.TypeChecking.Conversion.Errors where

import Control.Monad.Error.Class
import Control.Monad.Trans.Maybe
import Control.Monad.Except
import Control.Applicative
import Control.DeepSeq
import Control.Monad

import GHC.Generics (Generic)

import qualified Agda.Syntax.Common.Pretty as P
import Agda.Syntax.Internal
import Agda.Syntax.Common

import Agda.TypeChecking.Monad.Constraints
import Agda.TypeChecking.Monad.Statistics
import Agda.TypeChecking.Monad.SizedTypes
import Agda.TypeChecking.Monad.Signature
import Agda.TypeChecking.Monad.MetaVars
import Agda.TypeChecking.Monad.Builtin
import Agda.TypeChecking.Monad.Context
import Agda.TypeChecking.Monad.Debug
import Agda.TypeChecking.Monad.Pure
import Agda.TypeChecking.Monad.Base

import Agda.TypeChecking.Substitute
import Agda.TypeChecking.Telescope
import Agda.TypeChecking.Warnings
import Agda.TypeChecking.Records
import Agda.TypeChecking.Pretty

import Agda.Utils.Impossible
import Agda.Utils.Functor
import Agda.Utils.Maybe
import Agda.Utils.Monad hiding (guard)
import Agda.Utils.Size
import {-# SOURCE #-} Agda.TypeChecking.Errors
import Agda.TypeChecking.Monad.Closure

data FailedCompareAs
  = FailAsTermsOf Type Type
  | FailAsTypes (Maybe WhyUnequalTypes)
  deriving (Show, Generic)

data WhyUnequalTypes
  = forall a. (NFData a, Verbalize a) => UnequalDomain a a
  | UnequalHiding     Hiding Hiding
  | UnequalFiniteness Bool Bool

instance Show WhyUnequalTypes where
  show = const "<WhyUnequalTypes>"

instance NFData WhyUnequalTypes where
  rnf = \case
    UnequalDomain     a b -> rnf (a, b)
    UnequalHiding     a b -> rnf (a, b)
    UnequalFiniteness a b -> rnf (a, b)

instance PrettyTCM WhyUnequalTypes where
  prettyTCM = \case
    UnequalDomain a b -> fsep $
         pwords "one has "
      <> [text (verbalize a)]
      <> pwords "domain, while the other is "
      <> [text (verbalize b) <> "."]
    UnequalHiding a b -> fwords $ "one takes "
      <> verbalize (Indefinite a)
      <> " argument, while the other takes "
      <> verbalize (Indefinite b)
      <> " argument."
    UnequalFiniteness a b -> fsep
      let
        k True  p = pwords $ "a type of partial elements" <> p
        k False p = pwords $ "a function type" <> p
      in pwords "one is"
      <> k a ","
      <> pwords "while the other is"
      <> k b "."

instance P.Pretty FailedCompareAs where
  pretty = \case
    FailAsTypes{}     -> "(as types)"
    FailAsTermsOf a b -> P.pretty a P.<+> "," P.<+> P.pretty b

data ConversionZipper
  = ConvStop
  | ConvLam (Dom Type) (Abs Type) ArgName ConversionZipper
  | ConvDom (Dom ConversionZipper) (Abs Type) (Abs Type)
  | ConvCod (Dom Type) ArgName ConversionZipper
  | ConvApply Term (Abs Type) (Arg ConversionZipper) [Elim] [Elim]
  deriving (Show, Generic)

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

data ConversionError = ConversionError
  { convErrCmp   :: Comparison
  , convErrTys   :: FailedCompareAs
  , convErrLhs   :: Term
  , convErrRhs   :: Term
  , convErrCtx   :: Maybe ConversionZipper
  }
  deriving (Show, Generic)

instance NFData FailedCompareAs
instance NFData ConversionZipper
instance NFData ConversionError

failConversion :: (MonadTCError m, HasBuiltins m) => Comparison -> Term -> Term -> CompareAs -> m a
failConversion cmp l r cas = do
  as <- case cas of
    AsTypes     -> pure $ FailAsTypes Nothing
    AsTermsOf t -> pure $ FailAsTermsOf t t
    AsSizes     -> do
      t <- sizeType
      pure $ FailAsTermsOf t t

  typeError $ ConversionError_ ConversionError
    { convErrTys = as
    , convErrRhs = r
    , convErrLhs = l
    , convErrCmp = cmp
    , convErrCtx = Just ConvStop
    }

addConversionContext
  :: (MonadTCError m, HasBuiltins m)
  => (ConversionZipper -> ConversionZipper)
  -> m a
  -> m a
addConversionContext ext cont = cont `catchError` \case
  TypeError loc st cl'@Closure{ clValue = ConversionError_ conv@ConversionError{ convErrCtx = Just ctx } } -> do
    let
      zip   = ext ctx
      old_c = envCall (clEnv cl')
    cl <- buildClosure $ ConversionError_ conv { convErrCtx = Just zip }
    zip `seq` old_c `seq` throwError $ TypeError loc st cl
      { clEnv = (clEnv cl) { envCall = old_c }
      }
  err -> throwError err

cutConversionErrors :: (MonadPretty m, MonadError TCErr m) => m a -> m a
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

type ConversionProblem = (FailedCompareAs, Term, Term)

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
    failed = pure ( FailAsTermsOf t1 t2 , v1 , v2 )
  in
  fromMaybeM failed $ runMaybeT do
    t1 <- eliminateType mzero v1 t1 l_es
    t2 <- eliminateType mzero v2 t2 r_es
    pure
      ( FailAsTermsOf t1 t2
      , v1 `applyE` map (fmap blank) l_es
      , v2 `applyE` map (fmap blank) r_es
      )

mismatchedProjections
  :: (MonadError TCErr m, PureTCM m)
  => Type -> Term -> Elims
  -> Type -> Term -> Elims
  -> m a
mismatchedProjections t1 v1 e1 t2 v2 e2 = do
  (tys, lhs, rhs) <- eliminateLhsRhs t1 v1 e1 t2 v2 e2
  typeError $ ConversionError_ $ ConversionError CmpEq tys lhs rhs (Just ConvStop)

flattenConversionError :: forall m z. MonadPretty m => ConversionError -> (ConversionError -> m z) -> m z
flattenConversionError e@ConversionError{convErrCtx = Nothing} cont = cont e
flattenConversionError (ConversionError cmp tys lhs rhs (Just ctx)) cont =
  do
    reportSDoc "tc.conv.ctx" 30 $ vcat
      [ "env:" <+> (prettyTCM =<< getContextTelescope)
      , "tys:" <+> pretty tys
      , "lhs:" <+> pretty lhs
      , "rhs:" <+> pretty rhs
      , "ctx:" <+> prettyTCM ctx
      ]
    let
      k (tys, lhs, rhs) = do
        reportSDoc "tc.conv.ctx" 30 $ vcat
          [ "ctx:" <+> (prettyTCM =<< getContextTelescope)
          , "tys:" <+> pretty tys
          , "lhs:" <+> prettyTCM lhs
          , "rhs:" <+> prettyTCM rhs
          ]
        cont (ConversionError cmp (addHint tys lhs rhs) lhs rhs Nothing)
    go True (tys, lhs, rhs) ctx k k
  where

  addHint (FailAsTypes Nothing) (Pi dom1 _) (Pi dom2 _) = FailAsTypes $
    let
      hint :: (a -> a -> b) -> (forall x y. Dom' x y -> a) -> (a -> a -> Bool) -> Maybe b
      hint k g c = k (g dom1) (g dom2) <$ guard (not (c (g dom1) (g dom2)))
    in asum
      [ hint UnequalDomain     getRelevance     sameRelevance
      , hint UnequalDomain     getQuantity      sameQuantity
      , hint UnequalDomain     getModalPolarity samePolarity
      , hint UnequalDomain     getCohesion      sameCohesion
      , hint UnequalHiding     getHiding        sameHiding
      , hint UnequalFiniteness domIsFinite      (==)
      ]
  addHint x _ _ = x

  go
    :: forall z. Bool
    -> ConversionProblem
    -> ConversionZipper
    -> (ConversionProblem -> m z)
    -> (ConversionProblem -> m z)
    -> m z
  go toplevel prob@(tys, lhs, rhs) ctx err ok = case ctx of
    ConvStop -> ok (tys, lhs, rhs)

    -- Rules for skipping past uninteresting bits of context on the way
    -- to an implicit argument:
    ConvApply hd ty (Arg info rest) l_es r_es
      | toplevel, visible info                                   -> go toplevel prob rest err ok
      | toplevel, Con c o _ <- hd, IsRecord{} <- conDataRecord c -> go toplevel prob rest err ok
    ConvLam dom ty name rest | toplevel -> addContext (name, dom) $ go toplevel prob rest err ok
    ConvCod dom name rest    | toplevel -> addContext (name, dom) $ go toplevel prob rest err ok
    ConvDom dom c1 c2        | toplevel -> go toplevel prob (unDom dom) err ok

    -- Reconstructing subterm projections that the conversion checker
    -- does by hand:
    ConvLam dom ty name rest -> go toplevel prob rest (addContext (name, dom) . err) \case
      (FailAsTypes w, lhs, rhs) -> addContext (name, dom) $ ok (FailAsTypes w, lhs, rhs)
      (FailAsTermsOf a b, lhs, rhs) -> ok
        ( FailAsTermsOf
          (El (piSort (unEl <$> dom) (getSort dom) (getSort a <$ ty)) (Pi dom (a <$ ty)))
          (El (piSort (unEl <$> dom) (getSort dom) (getSort a <$ ty)) (Pi dom (a <$ ty)))
        , Lam (domInfo dom) (mkAbs name lhs)
        , Lam (domInfo dom) (mkAbs name rhs)
        )

    ConvDom dom c1 c2 -> go toplevel prob (unDom dom) err \(_, lhs, rhs) -> ok
      ( FailAsTypes Nothing
      , Pi (El __DUMMY_SORT__ lhs <$ dom) c1
      , Pi (El __DUMMY_SORT__ rhs <$ dom) c2
      )
    ConvCod dom name rest -> go toplevel prob rest err \(_, lhs, rhs) -> ok
      ( FailAsTypes Nothing
      , Pi dom (mkAbs name (El __DUMMY_SORT__ lhs))
      , Pi dom (mkAbs name (El __DUMMY_SORT__ rhs))
      )

    ConvApply hd ty (Arg info rest) l_es r_es -> go False prob rest err \prob@(_, lhs', rhs') ->
      let info' = info { argInfoOrigin = ConversionFail } in case hd of
        Def nm as | isExtendedLambdaName nm -> do
          ~Function{ funExtLam = Just (ExtLamInfo m b sys) } <- theDef <$> getConstInfo nm
          bs <- lookupSection m
          reportSDoc "tc.conv.ctx" 30 $ vcat
            [ "conversion context has extended lambda" <+> pretty nm
            , "bs " <> parens (pretty (size bs)) <> colon <> " " <> pretty bs
            , "as " <> parens (pretty (size as)) <> colon <> " " <> pretty as
            ]
          err prob
        _ -> ok =<< eliminateLhsRhs
          (ty `absApp` lhs') (hd `apply` [Arg info' lhs']) l_es
          (ty `absApp` rhs') (hd `apply` [Arg info' rhs']) r_es
