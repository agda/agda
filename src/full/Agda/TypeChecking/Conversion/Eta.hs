module Agda.TypeChecking.Conversion.Eta
  (EtaKit(..), etaKitForDef)
  where

import {-# SOURCE #-} Agda.TypeChecking.Conversion
import Agda.Syntax.Internal.Blockers
import Agda.Syntax.Internal
import Control.Monad.Trans.Maybe
import Control.Monad.Trans
import Control.Monad
import Agda.TypeChecking.Records
import Agda.Utils.Monad
import Agda.TypeChecking.Monad.Signature (usesCopatterns)
import Control.Applicative
import Agda.Syntax.Common
import Agda.TypeChecking.Monad.Builtin
import Agda.Utils.Impossible
import Agda.TypeChecking.Primitive
import Agda.TypeChecking.Substitute
import Agda.TypeChecking.Monad.Debug
import Agda.TypeChecking.Pretty
import Agda.Utils.Maybe
import Data.Char (toLower)

data EtaKit m = EtaKit
  { isNeutral        :: forall t. Args -> Blocked' t Term -> m Bool
  , isSingleton      :: Args -> m Bool
  , etaExpand        :: Args -> Term -> m (Telescope, Args)
  , headTerm         :: Args -> Term
  , profilingTickTag :: String -> String
  , verboseTag       :: String
  }

-- | Auxilliary function for defining 'EtaKit' for Cubical Agda types,
-- since those all have "constructors" given by a special Def (e.g. primGlue).
treatDefNeutral :: forall t m. MonadConversion m => QName -> Blocked' t Term -> m Bool
treatDefNeutral _    (NotBlocked _ Con{})     = pure False
treatDefNeutral name (NotBlocked _ (Def d _))
  | name == d = pure False
  | otherwise = not <$> usesCopatterns d
treatDefNeutral _ _ = pure True

recordEtaKit :: MonadConversion m => QName -> MaybeT m (EtaKit m)
recordEtaKit r = do
  guardM (isEtaRecord r)
  con <- getRecordConstructor r
  let
    kit = EtaKit
      { isNeutral = \_ -> \case
          -- Andreas, 2010-10-11: allowing neutrals to be blocked things does not seem
          -- to change Agda's behavior
          --    isNeutral Blocked{}          = False
          NotBlocked _ Con{} -> return False
          -- Andreas, 2013-09-18 / 2015-06-29: a Def by copatterns is
          -- not neutral if it is blocked (there can be missing projections
          -- to trigger a reduction.
          (NotBlocked r (Def q _)) -> -- Andreas, 2014-12-06 optimize this using r !!
            not <$> usesCopatterns q -- a def by copattern can reduce if projected
          _                   -> return True
      , isSingleton = \ps -> isSingletonRecordModuloRelevance r ps
      , etaExpand = etaExpandRecord r
      , headTerm = \_ -> Con con ConOSystem []
      , profilingTickTag = ("compare at eta record" ++)
      , verboseTag = "rec"
      }
  pure kit

newtypeEtaKit
  :: MonadConversion m
  => m (Maybe QName)                  -- ^ The type (e.g. Glue)
  -> m (Maybe QName)                  -- ^ The constructor (e.g. glue)
  -> m (Maybe QName)                  -- ^ The projection
  -> (QName -> Args -> Term -> Term) -- ^ Project the principal argument
  -> (Args -> Type)                  -- ^ Type of the principal argument
  -> String                          -- ^ Profiling tick tag
  -> Int
  -- ^ Index (zero-based) which the projection projects (so e.g. if @f
  -- (g x y z) = z@ and the rest don't matter, this argument would be 2)
  -> MaybeT m (QName -> MaybeT m (EtaKit m))
newtypeEtaKit tName con projnm proj projT desc idx = do
  [tName, con, projnm] <- traverse MaybeT [tName, con, projnm]
  let
    project :: Args -> Term -> (Telescope, Args)
    project ps tm = (ExtendTel (defaultDom (projT ps)) (Abs "g" EmptyTel), [unglued]) where
      unglued = case tm of
        Def con' as | con' == con, Just as <- allApplyElims as -> as !! idx
        _ -> argN (proj projnm ps tm)
  pure $ \nm -> do
    guard (nm == tName)
    pure EtaKit
      { isNeutral   = const (treatDefNeutral con)
      , isSingleton = \_ -> pure False
      , etaExpand   = \ps tm -> pure (project ps tm)
      , headTerm    = const (Def con [])
      , profilingTickTag = ("compare at " ++) . (desc ++)
      , verboseTag = map toLower (head (words desc))
      }

glueEtaKit :: MonadConversion m => MaybeT m (QName -> MaybeT m (EtaKit m))
glueEtaKit = newtypeEtaKit
  (getName' builtinGlue)
  (getName' builtin_glue)
  (getName' builtin_unglue)
  (\unglue ps tm -> Def unglue (map (Apply . setHiding Hidden) ps ++ [Apply (argN tm)]))
  (\(Arg _ la:_:Arg _ base:_) -> El (tmSort la) base)
  "Glue type"
  7

hcompUEtaKit :: MonadConversion m => MaybeT m (QName -> MaybeT m (EtaKit m))
hcompUEtaKit = do
  inS <- MaybeT $ getTerm' builtinSubIn
  outS <- MaybeT $ getTerm' builtinSubOut
  iz <- primIZero
  newtypeEtaKit
    (getName' builtinHComp)
    (getName' builtin_glueU)
    (getName' builtin_unglueU)
    (\unglue (sl:s:args@[phi, u, u0]) tm ->
      let
        Sort (Type lvl) = unArg s
        bA = inS `apply` [sl,s,phi,u0]
      in Def unglue [] `apply` ([argH (Level lvl)] ++ map (setHiding Hidden) [phi,u]  ++ [argH bA, argN tm]))
    (\(sl:s:args@[phi, u, u0]) -> let Sort (Type lvl) = unArg s in El (tmSort (Level lvl)) (unArg u0))
    "hcomp {Type}"
    5 -- glueU {la} {φ} {partial} {base} it

subEtaKit :: MonadConversion m => MaybeT m (QName -> MaybeT m (EtaKit m))
subEtaKit = do
  kit <- newtypeEtaKit
    (getName' builtinSub)
    (getName' builtinSubIn)
    (getName' builtinSubOut)
    (\unglue args tm ->
      Def unglue (map (Apply . setHiding Hidden) args ++ [Apply (argN tm)]))
    (\(l:a:_) -> El (tmSort (unArg l)) (unArg a))
    "Sub type"
    3 -- inS {la} {A} {φ} it
  pure $ \nm -> do
    sub <- MaybeT $ getName' builtinSub
    kit <- kit nm
    pure kit { isSingleton = \args -> isJust <$> isSingletonType (El (tmSSort __DUMMY_TERM__) (Def sub (map Apply args))) }

idEtaKit :: MonadConversion m => MaybeT m (QName -> MaybeT m (EtaKit m))
idEtaKit = do
  idT  <- getName' builtinId
  conid <- getName' builtinConId
  idp <- getTerm' "primIdPath"
  idf <- getTerm' "primIdFace"
  [idT, conid] <- traverse (MaybeT . pure) [idT, conid]
  [idp, idf] <- traverse (MaybeT . pure) [idp, idf]
  path <- getBuiltin builtinPath
  it <- primIntervalType
  cv <- conidView'
  let
    pathT l a x y = El (tmSort l) $ path `apply` [argH l, argH a, argN x, argN y]
  pure $ \tn -> do
    guard (tn == idT)
    pure EtaKit
      { isNeutral = \(l:a:x:_) e -> pure $ case e of
          NotBlocked ReallyNotBlocked tm@(Def q _) -> isNothing (cv (unArg x) tm)
          _ -> False
      , etaExpand = \[Arg _ l, Arg _ a, Arg _ x, Arg _ y] tm ->
          let
            ap = flip apply [argH l, argH a, argH x, argH y, argN tm]
            (phi, w) = case cv x tm of
              Just (phi, w) -> (argN (unArg phi), argN (unArg w))
              Nothing -> (argN (ap idf), argN (ap idp))
          in pure (ExtendTel (defaultDom it) (Abs "" (ExtendTel (defaultDom (pathT l a x y)) (Abs "" EmptyTel))), [phi, w])
      , isSingleton = const (pure False)
      , headTerm = Def conid . map (Apply . setHiding Hidden)
      , profilingTickTag = ("compare at Id type" ++)
      , verboseTag = "id"
      }

etaKitForDef :: MonadConversion m => QName -> m (Maybe (EtaKit m))
etaKitForDef r = do
  others <- catMaybes <$> traverse runMaybeT [glueEtaKit, hcompUEtaKit, subEtaKit, idEtaKit]
  runMaybeT $ recordEtaKit r <|> asum (map ($ r) others)
