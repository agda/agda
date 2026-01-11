module Agda.TypeChecking.Conversion.Errors
  ( ConversionError(..)
  , FailedCompareAs(..)
  , failConversion
  , mismatchedProjections
  , ConversionZipper(..)
  , cutConversionErrors, addConversionContext
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

-- |
data FailedCompareAs
  = FailAsTermsOf Type Type
  | FailAsTypes
  deriving (Show, Generic)

failCompareAs :: PureTCM m => CompareAs -> m FailedCompareAs
failCompareAs = \case
  AsTermsOf x -> pure $ FailAsTermsOf x x
  AsTypes     -> pure $ FailAsTypes
  AsSizes     -> do
    st <- sizeType
    pure $ FailAsTermsOf st st


instance PrettyTCM FailedCompareAs where
  prettyTCM = \case
    FailAsTypes{}     -> "(as types)"
    FailAsTermsOf a b -> prettyTCM a <+> comma <+> prettyTCM b

data ConversionZipper
  = ConvStop
  | ConvLam (Dom Type) (Abs Type) ArgName ConversionZipper
  | ConvCod (Dom Type) ArgName ConversionZipper
  | ConvDom (Dom ConversionZipper) (Abs Type) (Abs Type)
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

data HeadMismatch
  = HdmExtLam   QName QName
  | HdmTypes    WhyUnequalTypes
  | HdmVarDef | HdmDefVar | HdmVarCon | HdmConVar
  | HdmVars     Int   Int
  | HdmVarSpine Int (Closure (Elims, Elims))
  deriving (Show, Generic)

data HereOrThere = Here | There
  deriving (Show, Generic)

data ConversionErrorContext
  = Floating ConversionZipper
  | Finished HereOrThere (Maybe HeadMismatch)
  deriving (Show, Generic)

data ConversionError = ConversionError
  { convErrCmp   :: Comparison
  , convErrTys   :: FailedCompareAs
  , convErrLhs   :: Term
  , convErrRhs   :: Term
  , convErrCtx   :: ConversionErrorContext
  }
  deriving (Show, Generic)

instance NFData ConversionErrorContext
instance NFData ConversionZipper
instance NFData ConversionError
instance NFData FailedCompareAs
instance NFData HeadMismatch
instance NFData HereOrThere

failConversion :: (MonadTCError m, HasBuiltins m) => Comparison -> Term -> Term -> CompareAs -> m a
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

addConversionContext
  :: (MonadTCError m, HasBuiltins m)
  => (ConversionZipper -> ConversionZipper)
  -> m a
  -> m a
addConversionContext ext cont = cont `catchError` \case
  TypeError loc st cl'@Closure{ clValue = ConversionError_ conv@ConversionError{ convErrCtx = Floating ctx } } -> do
    let
      zip   = ext ctx
      old_c = envCall (clEnv cl')
    cl <- buildClosure $ ConversionError_ conv { convErrCtx = Floating zip }
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
  in
  fromMaybeT (FailAsTermsOf t1 t2, v1, v2) do
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
  typeError $ ConversionError_ $ ConversionError CmpEq tys lhs rhs (Floating ConvStop)

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
    , hint UnequalFiniteness domIsFinite      (==)
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
    go True ctx (k Here) k
  where
  go
    :: forall z. Bool
    -> ConversionZipper
    -> (Maybe HeadMismatch -> ConversionProblem -> m z)
    -> (HereOrThere -> Maybe HeadMismatch -> ConversionProblem -> m z)
    -> m z
  go toplevel ctx err ok = case ctx of
    ConvStop -> do
      reportSDoc "tc.conv.ctx" 30 $ vcat
        [ "reached center of conversion zipper:"
        , "  env:" <+> (prettyTCM =<< getContextTelescope)
        , "  tys:" <+> prettyTCM tys
        , "  lhs:" <+> pretty lhs
        , "  rhs:" <+> pretty rhs
        ]
      hdm <- runMaybeT $ headMismatch lhs rhs
      ok Here hdm (tys, lhs, rhs)

    -- Rules for skipping past uninteresting bits of context on the way
    -- to an implicit argument:
    ConvApply hd ty (Arg info rest) l_es r_es
      | toplevel, visible info                                   -> go toplevel rest err ok
      | toplevel, Con c o _ <- hd, IsRecord{} <- conDataRecord c -> go toplevel rest err ok
    ConvLam dom ty name rest | toplevel -> addContext (name, dom) $ go toplevel rest err ok
    ConvCod dom name rest    | toplevel -> addContext (name, dom) $ go toplevel rest err ok
    ConvDom dom c1 c2        | toplevel -> go toplevel (unDom dom) err ok

    -- Reconstructing subterm projections that the conversion checker
    -- does by hand:
    ConvLam dom ty name rest -> go toplevel rest (\hdm prob -> addContext (name, dom) $ err hdm prob)
      \ht hdm prob ->
      case prob of
        (FailAsTypes, lhs, rhs) -> addContext (name, dom) $ ok ht hdm (FailAsTypes, lhs, rhs)
        (FailAsTermsOf a b, lhs, rhs) -> ok There hdm
          ( FailAsTermsOf
            (El (piSort (unEl <$> dom) (getSort dom) (getSort a <$ ty)) (Pi dom (a <$ ty)))
            (El (piSort (unEl <$> dom) (getSort dom) (getSort a <$ ty)) (Pi dom (a <$ ty)))
          , Lam (domInfo dom) (mkAbs name lhs)
          , Lam (domInfo dom) (mkAbs name rhs)
          )

    ConvDom dom c1 c2 -> go toplevel (unDom dom) err \_ hdm (_, lhs, rhs) -> ok There hdm
      ( FailAsTypes
      , Pi (El __DUMMY_SORT__ lhs <$ dom) c1
      , Pi (El __DUMMY_SORT__ rhs <$ dom) c2
      )
    ConvCod dom name rest -> go toplevel rest err \_ hdm (_, lhs, rhs) -> ok There hdm
      ( FailAsTypes
      , Pi dom (mkAbs name (El __DUMMY_SORT__ lhs))
      , Pi dom (mkAbs name (El __DUMMY_SORT__ rhs))
      )

    ConvApply hd ty (Arg info rest) l_es r_es -> go False rest err \_ hdm prob@(_, lhs', rhs') ->
      let info' = info { argInfoOrigin = ConversionFail } in case hd of
        Def nm as | isExtendedLambdaName nm -> do
          ~Function{ funExtLam = Just (ExtLamInfo m b sys) } <- theDef <$> getConstInfo nm
          bs <- lookupSection m
          reportSDoc "tc.conv.ctx" 30 $ vcat
            [ "conversion context has extended lambda" <+> pretty nm
            , "bs " <> parens (pretty (size bs)) <> colon <> " " <> pretty bs
            , "as " <> parens (pretty (size as)) <> colon <> " " <> pretty as
            ]
          err hdm prob
        _ -> ok There hdm =<< eliminateLhsRhs
          (ty `absApp` lhs') (hd `apply` [Arg info' lhs']) l_es
          (ty `absApp` rhs') (hd `apply` [Arg info' rhs']) r_es

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
          , "are not equal at type " <> prettyTCM lhs_t <> orEmpty (comma <+> "because: " <$ disamb)
          , disambs
          ]
        _ -> vcat
          [ "The terms", nest 2 (pure d1 <+> colon <+> prettyTCM lhs_t)
          , "and",       nest 2 (pure d2 <+> colon <+> prettyTCM rhs_t)
          , "are not equal" <> orEmpty (comma <+> "because: " <$ disamb)
          , disambs
          ]
      FailAsTypes | CmpEq <- cmp -> vcat
        [ "The" <+> case what of
            Just UnequalDomain{} -> "function types"
            Just UnequalHiding{} -> "function types"
            _ -> "types"
        , nest 2 (pure d1), "and", nest 2 (pure d2)
        , "are not equal" <> orEmpty (comma <+> "because: " <$ disamb)
        , disambs
        ]
      FailAsTypes | CmpLeq <- cmp -> vcat
        [ "The" <+> case what of
            Just UnequalDomain{} -> "function type"
            Just UnequalHiding{} -> "function type"
            _ -> "type"
        , nest 2 (pure d1), "is not a subtype of", nest 2 (pure d2)
        , orEmpty ("because:" <$ what)
        , disambs
        ]

displayDisamb
  :: forall m. MonadPretty m
  => HereOrThere
  -> Maybe (Int, Closure (Elims, Elims))
  -> Term -> Term
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

    redisplay :: MaybeT m Doc
    redisplay = do
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

  (d1, d2,) <$> runMaybeT do
    guard (P.render d1 == P.render d2)
    reportSDoc "tc.error.conv" 30 $ vcat
      [ "terms rendered the same"
      , "  t1:" <+> pretty t1
      , "  d1:" <+> pure d1
      , "  t2:" <+> pretty t2
      , "  d2:" <+> pure d2
      ]
    redisplay

-- | Print two terms that are supposedly unequal.
--   If they print to the same identifier, add some explanation
--   why they are different nevertheless.
prettyInEqual
  :: MonadPretty m
  => HereOrThere
  -> Maybe HeadMismatch
  -> Term -> Term -> m (Doc, Doc, Maybe Doc)
prettyInEqual ht hdm t1 t2
  | Nothing                 <- hdm = displayDisamb ht Nothing t1 t2
  | Just (HdmVarSpine i cl) <- hdm = displayDisamb ht (Just (i, cl)) t1 t2
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
          <> [hlKeyword (text (verbalize (Indefinite b))), "argument"]
        UnequalFiniteness a b ->
          let
            k True  p = pwords $ "a type of partial elements" <> p
            k False p = pwords $ "a function type" <> p
          in pwords "one is" <> k a "," <> pwords "while the other is" <> k b "."
      explain = case ht of
        Here  -> fsep ecore
        There -> fsep $ pwords "the mismatched terms are function types, and" <> ecore
    in (,,) <$> prettyTCMCtx TopCtx t1 <*> prettyTCMCtx TopCtx t2 <*> (Just <$> explain)
prettyInEqual ht (Just hdm) t1 t2 = do
  d1 <- prettyTCMCtx TopCtx t1
  d2 <- prettyTCMCtx TopCtx t2
  (d1, d2,) <$> runMaybeT do
    guard (P.render d1 /= P.render d2)
    case hdm of
      HdmVars   i j -> fwords $ "one has de Bruijn index " ++ show i ++ " and the other " ++ show j
      HdmExtLam a b -> vcat
        [ fwords "the mismatched terms are distinct extended lambdas"
        , fwords "one is defined at"
        , "  " <+> pretty (nameBindingSite (qnameName a))
        , fwords "and the other at"
        , "  " <+> (pretty (nameBindingSite (qnameName b)) <> ",")
        , fwords "so they have different internal representations."
        ]
      HdmVarDef -> fwords "one is a variable, the other a definition"
      HdmVarCon -> fwords "one is a variable, the other a constructor"
      HdmDefVar -> fwords "one is a definition, the other a variable"
      HdmConVar -> fwords "one is a constructor, the other a variable"
