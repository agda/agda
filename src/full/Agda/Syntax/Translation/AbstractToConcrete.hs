{-# LANGUAGE CPP          #-}

-- {-# OPTIONS -fwarn-unused-binds #-}

{-| The translation of abstract syntax to concrete syntax has two purposes.
    First it allows us to pretty print abstract syntax values without having to
    write a dedicated pretty printer, and second it serves as a sanity check
    for the concrete to abstract translation: translating from concrete to
    abstract and then back again should be (more or less) the identity.
-}
module Agda.Syntax.Translation.AbstractToConcrete
    ( ToConcrete(..)
    , toConcreteCtx
    , abstractToConcrete_
    , abstractToConcreteScope
    , abstractToConcreteHiding
    , runAbsToCon
    , RangeAndPragma(..)
    , abstractToConcreteCtx
    , withScope
    , preserveInteractionIds
    , MonadAbsToCon, AbsToCon, Env
    , noTakenNames
    , lookupQName
    ) where

import Prelude hiding (null)

import Control.Arrow        ( (&&&), first )
import Control.Monad        ( (<=<), forM, forM_, guard, liftM2 )
import Control.Monad.Except ( runExceptT )
import Control.Monad.Reader ( MonadReader(..), asks, runReaderT )
import Control.Monad.State  ( StateT(..), runStateT )

import qualified Control.Monad.Fail as Fail

import qualified Data.Map as Map
import Data.Maybe
import Data.Monoid hiding ((<>))
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Map (Map)
import qualified Data.Foldable as Fold
import Data.Void
import Data.List (sortBy)
import Data.Semigroup (Semigroup, (<>))
import Data.String

import Agda.Syntax.Common
import Agda.Syntax.Position
import Agda.Syntax.Literal
import Agda.Syntax.Info as A
import qualified Agda.Syntax.Internal as I
import Agda.Syntax.Fixity
import Agda.Syntax.Concrete as C
import Agda.Syntax.Concrete.Pattern as C
import Agda.Syntax.Concrete.Glyph
import Agda.Syntax.Abstract as A
import Agda.Syntax.Abstract.Views as A
import Agda.Syntax.Abstract.Pattern as A
import Agda.Syntax.Abstract.PatternSynonyms
import Agda.Syntax.Scope.Base
import Agda.Syntax.Scope.Monad ( tryResolveName )

import Agda.TypeChecking.Monad.State (getScope, getAllPatternSyns)
import Agda.TypeChecking.Monad.Base
import Agda.TypeChecking.Monad.Context
import Agda.TypeChecking.Monad.Debug
import Agda.TypeChecking.Monad.Builtin
import Agda.TypeChecking.Monad.MetaVars
import Agda.TypeChecking.Monad.Pure
import Agda.TypeChecking.Monad.Signature
import {-# SOURCE #-} Agda.TypeChecking.Pretty (prettyTCM)
import Agda.Interaction.Options

import qualified Agda.Utils.AssocList as AssocList
import Agda.Utils.Either
import Agda.Utils.Function
import Agda.Utils.Functor
import Agda.Utils.Lens
import Agda.Utils.List1 (List1, pattern (:|), (<|) )
import Agda.Utils.List2 (List2, pattern List2)
import qualified Agda.Utils.List1 as List1
import Agda.Utils.Maybe
import Agda.Utils.Monad
import Agda.Utils.Null
import Agda.Utils.Pretty hiding ((<>))
import Agda.Utils.Singleton
import Agda.Utils.Suffix

import Agda.Utils.Impossible

-- Environment ------------------------------------------------------------

data Env = Env { takenVarNames :: Set A.Name
                  -- ^ Abstract names currently in scope. Unlike the
                  --   ScopeInfo, this includes names for hidden
                  --   arguments inserted by the system.
               , takenDefNames :: Set C.NameParts
                  -- ^ Concrete names of all definitions in scope
               , currentScope :: ScopeInfo
               , builtins     :: Map BuiltinId A.QName
                  -- ^ Certain builtins (like `fromNat`) have special printing
               , preserveIIds :: Bool
                  -- ^ Preserve interaction point ids
               , foldPatternSynonyms :: Bool
               }

makeEnv :: MonadAbsToCon m => ScopeInfo -> m Env
makeEnv scope = do
      -- zero and suc doesn't have to be in scope for natural number literals to work
  let noScopeCheck b = b `elem` [builtinZero, builtinSuc]
      name (I.Def q _)   = Just q
      name (I.Con q _ _) = Just (I.conName q)
      name _             = Nothing
      builtin b = getBuiltin' b >>= \ case
        Just v | Just q <- name v,
                 noScopeCheck b || isNameInScope q scope -> return [(b, q)]
        _                                                -> return []
  ctxVars <- map (fst . I.unDom) <$> asksTC envContext
  letVars <- Map.keys <$> asksTC envLetBindings
  let vars = ctxVars ++ letVars

  -- pick concrete names for in-scope names now so we don't
  -- accidentally shadow them
  forM_ (scope ^. scopeLocals) $ \(y , x) -> do
    pickConcreteName (localVar x) y

  builtinList <- concat <$> mapM builtin [ builtinFromNat, builtinFromString, builtinFromNeg, builtinZero, builtinSuc ]
  foldPatSyns <- optPrintPatternSynonyms <$> pragmaOptions
  return $
    Env { takenVarNames = Set.fromList vars
        , takenDefNames = defs
        , currentScope = scope
        , builtins     = Map.fromListWith __IMPOSSIBLE__ builtinList
        , preserveIIds = False
        , foldPatternSynonyms = foldPatSyns
        }
  where
    defs = Set.map nameParts . Map.keysSet $
        Map.filterWithKey usefulDef $
        nsNames $ everythingInScope scope

    -- Jesper, 2018-12-10: It's fine to shadow generalizable names as
    -- they will never show up directly in printed terms.
    notGeneralizeName AbsName{ anameKind = k }  =
      not (k == GeneralizeName || k == DisallowedGeneralizeName)

    usefulDef C.NoName{} _ = False
    usefulDef C.Name{} names = all notGeneralizeName names

    nameParts (C.NoName {}) = __IMPOSSIBLE__
    nameParts (C.Name { nameNameParts }) = nameNameParts

currentPrecedence :: AbsToCon PrecedenceStack
currentPrecedence = asks $ (^. scopePrecedence) . currentScope

preserveInteractionIds :: AbsToCon a -> AbsToCon a
preserveInteractionIds = local $ \ e -> e { preserveIIds = True }

withPrecedence' :: PrecedenceStack -> AbsToCon a -> AbsToCon a
withPrecedence' ps = local $ \e ->
  e { currentScope = set scopePrecedence ps (currentScope e) }

withPrecedence :: Precedence -> AbsToCon a -> AbsToCon a
withPrecedence p ret = do
  ps <- currentPrecedence
  withPrecedence' (pushPrecedence p ps) ret

withScope :: ScopeInfo -> AbsToCon a -> AbsToCon a
withScope scope = local $ \e -> e { currentScope = scope }

noTakenNames :: AbsToCon a -> AbsToCon a
noTakenNames = local $ \e -> e { takenVarNames = Set.empty }

dontFoldPatternSynonyms :: AbsToCon a -> AbsToCon a
dontFoldPatternSynonyms = local $ \ e -> e { foldPatternSynonyms = False }

-- | Bind a concrete name to an abstract in the translation environment.
addBinding :: C.Name -> A.Name -> Env -> Env
addBinding y x e =
  e { takenVarNames = Set.insert x $ takenVarNames e
    , currentScope = (`updateScopeLocals` currentScope e) $
        AssocList.insert y (LocalVar x __IMPOSSIBLE__ [])
    }

-- | Get a function to check if a name refers to a particular builtin function.
isBuiltinFun :: AbsToCon (A.QName -> BuiltinId -> Bool)
isBuiltinFun = asks $ is . builtins
  where is m q b = Just q == Map.lookup b m

-- | Resolve a concrete name. If illegally ambiguous fail with the ambiguous names.
resolveName :: KindsOfNames -> Maybe (Set A.Name) -> C.QName -> AbsToCon (Either AmbiguousNameReason ResolvedName)
resolveName kinds candidates q = runExceptT $ tryResolveName kinds candidates q

-- | Treat illegally ambiguous names as UnknownNames.
resolveName_ :: C.QName -> [A.Name] -> AbsToCon ResolvedName
resolveName_ q cands = fromRight (const UnknownName) <$> resolveName allKindsOfNames (Just $ Set.fromList cands) q

-- The Monad --------------------------------------------------------------

-- | The function 'runAbsToCon' can target any monad that satisfies
-- the constraints of 'MonadAbsToCon'.
type MonadAbsToCon m =
  ( MonadFresh NameId m
  , MonadInteractionPoints m
  , MonadStConcreteNames m
  , HasOptions m
  , PureTCM m
  , IsString (m Doc)
  , Null (m Doc)
  , Semigroup (m Doc)
  )

newtype AbsToCon a = AbsToCon
  { unAbsToCon :: forall m.
      ( MonadReader Env m
      , MonadAbsToCon m
      ) => m a
  }

-- TODO: Is there some way to automatically derive these boilerplate
-- instances?  GeneralizedNewtypeDeriving fails us here.
instance Functor AbsToCon where
  fmap f x = AbsToCon $ f <$> unAbsToCon x

instance Applicative AbsToCon where
  pure x = AbsToCon $ pure x
  f <*> m = AbsToCon $ unAbsToCon f <*> unAbsToCon m

instance Monad AbsToCon where
  -- ASR (2021-02-07). The eta-expansion @\m' -> unAbsToCon m'@ is
  -- required by GHC >= 9.0.1 (see Issue #4955).
  m >>= f = AbsToCon $ unAbsToCon m >>= (\m' -> unAbsToCon m'). f
#if __GLASGOW_HASKELL__ < 808
  fail = Fail.fail
#endif

instance Fail.MonadFail AbsToCon where
  fail = error

instance MonadReader Env AbsToCon where
  ask = AbsToCon ask
  local f m = AbsToCon $ local f $ unAbsToCon m

instance MonadTCEnv AbsToCon where
  askTC = AbsToCon askTC
  localTC f m = AbsToCon $ localTC f $ unAbsToCon m

instance ReadTCState AbsToCon where
  getTCState = AbsToCon getTCState
  locallyTCState l f m = AbsToCon $ locallyTCState l f $ unAbsToCon m

instance MonadStConcreteNames AbsToCon where
  -- ASR (2021-02-07). The eta-expansion @\m' -> unAbsToCon m'@ is
  -- required by GHC >= 9.0.1 (see Issue #4955).
  runStConcreteNames m =
    AbsToCon $ runStConcreteNames $ StateT $ (\m' -> unAbsToCon m') . runStateT m

instance HasBuiltins AbsToCon where
  getBuiltinThing x = AbsToCon $ getBuiltinThing x

instance HasOptions AbsToCon where
  pragmaOptions = AbsToCon pragmaOptions
  commandLineOptions = AbsToCon commandLineOptions

instance MonadDebug AbsToCon where
  formatDebugMessage k n s      = AbsToCon $ formatDebugMessage k n s
  traceDebugMessage  k n s cont = AbsToCon $ traceDebugMessage  k n s $ unAbsToCon cont  -- can't eta-reduce!
  verboseBracket     k n s cont = AbsToCon $ verboseBracket     k n s $ unAbsToCon cont  -- because of GHC-9.0

  getVerbosity      = defaultGetVerbosity
  getProfileOptions = defaultGetProfileOptions
  isDebugPrinting   = defaultIsDebugPrinting
  nowDebugPrinting  = defaultNowDebugPrinting

instance HasConstInfo AbsToCon where
  getConstInfo' a      = AbsToCon (getConstInfo' a)
  getRewriteRulesFor a = AbsToCon (getRewriteRulesFor a)

instance MonadAddContext AbsToCon where
  addCtx a b c = AbsToCon (addCtx a b (unAbsToCon c))

  addLetBinding' o a b c d =
    AbsToCon (addLetBinding' o a b c (unAbsToCon d))

  updateContext a b c = AbsToCon (updateContext a b (unAbsToCon c))

  withFreshName a b c =
    AbsToCon (withFreshName a b (\x -> unAbsToCon (c x)))

instance MonadReduce AbsToCon where
  liftReduce a = AbsToCon (liftReduce a)

instance PureTCM AbsToCon where

instance MonadFresh NameId AbsToCon where
  fresh = AbsToCon fresh

instance MonadInteractionPoints AbsToCon where
  freshInteractionId        = AbsToCon freshInteractionId
  modifyInteractionPoints a = AbsToCon (modifyInteractionPoints a)

instance IsString (AbsToCon Doc) where
  fromString a = AbsToCon (fromString a)

instance Null (AbsToCon Doc) where
  empty = AbsToCon empty
  null  = __IMPOSSIBLE__

instance Semigroup (AbsToCon Doc) where
  a <> b = AbsToCon (unAbsToCon a <> unAbsToCon b)

runAbsToCon :: MonadAbsToCon m => AbsToCon c -> m c
runAbsToCon m = do
  scope <- getScope
  verboseBracket "toConcrete" 50 "runAbsToCon" $ do
    reportSLn "toConcrete" 50 $ render $ hsep $
      [ "entering AbsToCon with scope:"
      , prettyList_ (map (text . C.nameToRawName . fst) $ scope ^. scopeLocals)
      ]
    x <- runReaderT (unAbsToCon m) =<< makeEnv scope
    reportSLn "toConcrete" 50 $ "leaving AbsToCon"
    return x

abstractToConcreteScope :: (ToConcrete a, MonadAbsToCon m)
                        => ScopeInfo -> a -> m (ConOfAbs a)
abstractToConcreteScope scope a = runReaderT (unAbsToCon $ toConcrete a) =<< makeEnv scope

abstractToConcreteCtx :: (ToConcrete a, MonadAbsToCon m)
                      => Precedence -> a -> m (ConOfAbs a)
abstractToConcreteCtx ctx x = runAbsToCon $ withPrecedence ctx (toConcrete x)

abstractToConcrete_ :: (ToConcrete a, MonadAbsToCon m)
                    => a -> m (ConOfAbs a)
abstractToConcrete_ = runAbsToCon . toConcrete

abstractToConcreteHiding :: (LensHiding i, ToConcrete a, MonadAbsToCon m)
                         => i -> a -> m (ConOfAbs a)
abstractToConcreteHiding i = runAbsToCon . toConcreteHiding i

-- Dealing with names -----------------------------------------------------

-- | Names in abstract syntax are fully qualified, but the concrete syntax
--   requires non-qualified names in places. In theory (if all scopes are
--   correct), we should get a non-qualified name when translating back to a
--   concrete name, but I suspect the scope isn't always perfect. In these
--   cases we just throw away the qualified part. It's just for pretty printing
--   anyway...
unsafeQNameToName :: C.QName -> C.Name
unsafeQNameToName = C.unqualify

lookupQName :: AllowAmbiguousNames -> A.QName -> AbsToCon C.QName
lookupQName ambCon x | Just s <- getGeneralizedFieldName x =
  return (C.QName $ C.Name noRange C.InScope $ C.stringNameParts s)
lookupQName ambCon x = do
  ys <- asks (inverseScopeLookupName' ambCon x . currentScope)
  reportSLn "scope.inverse" 100 $
    "inverse looking up abstract name " ++ prettyShow x ++ " yields " ++ prettyShow ys
  loop ys

  where
    -- Found concrete name: check that it is not shadowed by a local
    loop (qy@Qual{}      : _ ) = return qy -- local names cannot be qualified
    loop (qy@(C.QName y) : ys) = lookupNameInScope y >>= \case
      Just x' | x' /= qnameName x -> loop ys
      _ -> return qy
    -- Found no concrete name: make up a new one
    loop [] = case qnameToConcrete x of
      qy@Qual{}    -> return $ setNotInScope qy
      qy@C.QName{} -> C.QName <$> chooseName (qnameName x)

lookupModule :: A.ModuleName -> AbsToCon C.QName
lookupModule (A.MName []) = return $ C.QName $ C.simpleName "-1"
  -- Andreas, 2016-10-10 it can happen that we have an empty module name
  -- for instance when we query the current module inside the
  -- frontmatter or module telescope of the top level module.
  -- In this case, we print it as an invalid module name.
  -- (Should only affect debug printing.)
lookupModule x =
    do  scope <- asks currentScope
        case inverseScopeLookupModule x scope of
            (y : _) -> return y
            []      -> return $ mnameToConcrete x
                -- this is what happens for names that are not in scope (private names)

-- | Is this concrete name currently in use by a particular abstract
--   name in the current scope?
lookupNameInScope :: C.Name -> AbsToCon (Maybe A.Name)
lookupNameInScope y =
  asks ((fmap localVar . lookup y) . ((^. scopeLocals) . currentScope))

-- | Have we already committed to a specific concrete name for this
--   abstract name? If yes, return the concrete name(s).
hasConcreteNames :: (MonadStConcreteNames m) => A.Name -> m [C.Name]
hasConcreteNames x = Map.findWithDefault [] x <$> useConcreteNames

-- | Commit to a specific concrete name for printing the given
--   abstract name. If the abstract name already has associated
---  concrete name(s), the new name is only used when all previous
---  names are shadowed. Precondition: the abstract name should be in
--   scope.
pickConcreteName :: (MonadStConcreteNames m) => A.Name -> C.Name -> m ()
pickConcreteName x y = modifyConcreteNames $ flip Map.alter x $ \case
    Nothing   -> Just $ [y]
    (Just ys) -> Just $ ys ++ [y]

-- | For the given abstract name, return the names that could shadow it.
shadowingNames :: (ReadTCState m, MonadStConcreteNames m)
               => A.Name -> m (Set RawName)
shadowingNames x =
  Set.fromList . Fold.toList . Map.findWithDefault mempty x <$>
    useR stShadowingNames

toConcreteName :: A.Name -> AbsToCon C.Name
toConcreteName x | y <- nameConcrete x , isNoName y = return y
toConcreteName x = (Map.findWithDefault [] x <$> useConcreteNames) >>= loop
  where
    -- case: we already have picked some name(s) for x
    loop (y:ys) = ifM (isGoodName x y) (return y) (loop ys)

    -- case: we haven't picked a concrete name yet, or all previously
    -- picked names are shadowed, so we pick a new name now
    loop [] = do
      y <- chooseName x
      pickConcreteName x y
      return y

    -- Is 'y' a good concrete name for abstract name 'x'?
    isGoodName :: A.Name -> C.Name -> AbsToCon Bool
    isGoodName x y = do
      zs <- asks (Set.toList . takenVarNames)
      allM zs $ \z -> if x == z then return True else do
        czs <- hasConcreteNames z
        return $ notElem y czs


-- | Choose a new unshadowed name for the given abstract name
-- | NOTE: See @withName@ in @Agda.Syntax.Translation.ReflectedToAbstract@ for similar logic.
-- | NOTE: See @freshConcreteName@ in @Agda.Syntax.Scope.Monad@ also for similar logic.
chooseName :: A.Name -> AbsToCon C.Name
chooseName x = lookupNameInScope (nameConcrete x) >>= \case
  -- If the name is currently in scope, we do not rename it
  Just x' | x == x' -> do
    reportSLn "toConcrete.bindName" 80 $
      "name " ++ C.nameToRawName (nameConcrete x) ++ " already in scope, so not renaming"
    return $ nameConcrete x
  -- Otherwise we pick a name that does not shadow other names
  _ -> do
    takenDefs <- asks takenDefNames
    taken   <- takenNames
    toAvoid <- shadowingNames x
    glyphMode <- optUseUnicode <$> pragmaOptions
    let freshNameMode = case glyphMode of
          UnicodeOk -> A.UnicodeSubscript
          AsciiOnly -> A.AsciiCounter

        shouldAvoid C.NoName {} = False
        shouldAvoid name@C.Name { nameNameParts } =
          let raw = C.nameToRawName name in
          nameNameParts `Set.member` takenDefs ||
          raw `Set.member` taken ||
          raw `Set.member` toAvoid

        y = firstNonTakenName freshNameMode shouldAvoid $ nameConcrete x
    reportSLn "toConcrete.bindName" 80 $ render $ vcat
      [ "picking concrete name for:" <+> text (C.nameToRawName $ nameConcrete x)
      , "names already taken:      " <+> prettyList_ (Set.toList taken)
      , "names to avoid:           " <+> prettyList_ (Set.toList toAvoid)
      , "concrete name chosen:     " <+> text (C.nameToRawName y)
      ]
    return y

  where
    takenNames :: AbsToCon (Set RawName)
    takenNames = do
      ys0 <- asks takenVarNames
      reportSLn "toConcrete.bindName" 90 $ render $ "abstract names of local vars: " <+> prettyList_ (map (C.nameToRawName . nameConcrete) $ Set.toList ys0)
      ys <- Set.fromList . concat <$> mapM hasConcreteNames (Set.toList ys0)
      return $ Set.map C.nameToRawName ys


-- | Add a abstract name to the scope and produce an available concrete version of it.
bindName :: A.Name -> (C.Name -> AbsToCon a) -> AbsToCon a
bindName x ret = do
  y <- toConcreteName x
  reportSLn "toConcrete.bindName" 30 $ "adding " ++ C.nameToRawName (nameConcrete x) ++ " to the scope under concrete name " ++ C.nameToRawName y
  local (addBinding y x) $ ret y

-- | Like 'bindName', but do not care whether name is already taken.
bindName' :: A.Name -> AbsToCon a -> AbsToCon a
bindName' x ret = do
  reportSLn "toConcrete.bindName" 30 $ "adding " ++ C.nameToRawName (nameConcrete x) ++ " to the scope with forced name"
  pickConcreteName x y
  applyUnless (isNoName y) (local $ addBinding y x) ret
  where y = nameConcrete x

-- Dealing with precedences -----------------------------------------------

-- | General bracketing function.
bracket' ::    (e -> e)             -- ^ the bracketing function
            -> (PrecedenceStack -> Bool) -- ^ Should we bracket things
                                    --   which have the given
                                    --   precedence?
            -> e -> AbsToCon e
bracket' paren needParen e =
    do  p <- currentPrecedence
        return $ if needParen p then paren e else e

-- | Expression bracketing
bracket :: (PrecedenceStack -> Bool) -> AbsToCon C.Expr -> AbsToCon C.Expr
bracket par m =
    do  e <- m
        bracket' (Paren (getRange e)) par e

-- | Pattern bracketing
bracketP_ :: (PrecedenceStack -> Bool) -> AbsToCon C.Pattern -> AbsToCon C.Pattern
bracketP_ par m =
    do  e <- m
        bracket' (ParenP (getRange e)) par e

{- UNUSED
-- | Pattern bracketing
bracketP :: (PrecedenceStack -> Bool) -> (C.Pattern -> AbsToCon a)
                                 -> ((C.Pattern -> AbsToCon a) -> AbsToCon a)
                                 -> AbsToCon a
bracketP par ret m = m $ \p -> do
    p <- bracket' (ParenP $ getRange p) par p
    ret p
-}

-- | Applications where the argument is a lambda without parentheses need
--   parens more often than other applications.
isLambda :: NamedArg A.Expr -> Bool
isLambda e | notVisible e = False
isLambda e =
  case unScope $ namedArg e of
    A.Lam{}         -> True
    A.AbsurdLam{}   -> True
    A.ExtendedLam{} -> True
    _               -> False

-- Dealing with infix declarations ----------------------------------------

-- | If a name is defined with a fixity that differs from the default, we have
--   to generate a fixity declaration for that name.
withInfixDecl :: DefInfo -> C.Name -> AbsToCon [C.Declaration] -> AbsToCon [C.Declaration]
withInfixDecl i x m = ((fixDecl ++ synDecl) ++) <$> m
  where
  fixDecl = [ C.Infix (theFixity $ defFixity i) $ singleton x
            | theFixity (defFixity i) /= noFixity
            ]
  synDecl = [ C.Syntax x $ theNotation $ defFixity i ]

-- Dealing with private definitions ---------------------------------------

-- | Add @abstract@, @private@, @instance@ modifiers.
withAbstractPrivate :: DefInfo -> AbsToCon [C.Declaration] -> AbsToCon [C.Declaration]
withAbstractPrivate i m =
    priv (defAccess i)
      . abst (A.defAbstract i)
      . addInstanceB (case A.defInstance i of InstanceDef r -> Just r; NotInstanceDef -> Nothing)
      <$> m
    where
        priv (PrivateAccess UserWritten)
                         ds = [ C.Private  (getRange ds) UserWritten ds ]
        priv _           ds = ds
        abst AbstractDef ds = [ C.Abstract (getRange ds) ds ]
        abst ConcreteDef ds = ds

addInstanceB :: Maybe Range -> [C.Declaration] -> [C.Declaration]
addInstanceB (Just r) ds = [ C.InstanceB r ds ]
addInstanceB Nothing  ds = ds

-- The To Concrete Class --------------------------------------------------

class ToConcrete a where
    type ConOfAbs a
    toConcrete :: a -> AbsToCon (ConOfAbs a)
    bindToConcrete :: a -> (ConOfAbs a -> AbsToCon b) -> AbsToCon b

    -- Christian Sattler, 2017-08-05:
    -- These default implementations are not valid semantically (at least
    -- the second one). Perhaps they (it) should be removed.
    toConcrete     x     = bindToConcrete x return
    bindToConcrete x ret = ret =<< toConcrete x

-- | Translate something in a context of the given precedence.
toConcreteCtx :: ToConcrete a => Precedence -> a -> AbsToCon (ConOfAbs a)
toConcreteCtx p x = withPrecedence p $ toConcrete x

-- | Translate something in a context of the given precedence.
bindToConcreteCtx :: ToConcrete a => Precedence -> a -> (ConOfAbs a -> AbsToCon b) -> AbsToCon b
bindToConcreteCtx p x ret = withPrecedence p $ bindToConcrete x ret

-- | Translate something in the top context.
toConcreteTop :: ToConcrete a => a -> AbsToCon (ConOfAbs a)
toConcreteTop = toConcreteCtx TopCtx

-- | Translate something in the top context.
bindToConcreteTop :: ToConcrete a => a -> (ConOfAbs a -> AbsToCon b) -> AbsToCon b
bindToConcreteTop = bindToConcreteCtx TopCtx

-- | Translate something in a context indicated by 'Hiding' info.
toConcreteHiding :: (LensHiding h, ToConcrete a) => h -> a -> AbsToCon (ConOfAbs a)
toConcreteHiding h =
  case getHiding h of
    NotHidden  -> toConcrete
    Hidden     -> toConcreteTop
    Instance{} -> toConcreteTop

-- | Translate something in a context indicated by 'Hiding' info.
bindToConcreteHiding :: (LensHiding h, ToConcrete a) => h -> a -> (ConOfAbs a -> AbsToCon b) -> AbsToCon b
bindToConcreteHiding h =
  case getHiding h of
    NotHidden  -> bindToConcrete
    Hidden     -> bindToConcreteTop
    Instance{} -> bindToConcreteTop

-- General instances ------------------------------------------------------

instance ToConcrete () where
  type ConOfAbs () = ()
  toConcrete = pure

instance ToConcrete Bool where
  type ConOfAbs Bool = Bool
  toConcrete = pure

instance ToConcrete a => ToConcrete [a] where
    type ConOfAbs [a] = [ConOfAbs a]

    toConcrete     = mapM toConcrete
    bindToConcrete []     ret = ret []
    bindToConcrete (a:as) ret = bindToConcrete (a:|as) $ \ (c:|cs) -> ret (c:cs)

instance ToConcrete a => ToConcrete (List1 a) where
    type ConOfAbs (List1 a) = List1 (ConOfAbs a)

    toConcrete     = mapM toConcrete
    -- Andreas, 2017-04-11, Issue #2543
    -- The naive `thread'ing does not work as we have to undo
    -- changes to the Precedence.
    -- bindToConcrete = thread bindToConcrete
    bindToConcrete (a :| as) ret = do
      p <- currentPrecedence  -- save precedence
      bindToConcrete a $ \ c ->
        withPrecedence' p $ -- reset precedence
          bindToConcrete as $ \ cs ->
            ret (c :| cs)

instance (ToConcrete a1, ToConcrete a2) => ToConcrete (Either a1 a2) where
    type ConOfAbs (Either a1 a2) = Either (ConOfAbs a1) (ConOfAbs a2)

    toConcrete = traverseEither toConcrete toConcrete
    bindToConcrete (Left x) ret =
        bindToConcrete x $ \x ->
        ret (Left x)
    bindToConcrete (Right y) ret =
        bindToConcrete y $ \y ->
        ret (Right y)

instance (ToConcrete a1, ToConcrete a2) => ToConcrete (a1, a2) where
    type ConOfAbs (a1, a2) = (ConOfAbs a1, ConOfAbs a2)

    toConcrete (x,y) = liftM2 (,) (toConcrete x) (toConcrete y)
    bindToConcrete (x,y) ret =
        bindToConcrete x $ \x ->
        bindToConcrete y $ \y ->
        ret (x,y)

instance (ToConcrete a1, ToConcrete a2, ToConcrete a3) => ToConcrete (a1,a2,a3) where
    type ConOfAbs (a1, a2, a3) = (ConOfAbs a1, ConOfAbs a2, ConOfAbs a3)

    toConcrete (x,y,z) = reorder <$> toConcrete (x,(y,z))
        where
            reorder (x,(y,z)) = (x,y,z)

    bindToConcrete (x,y,z) ret = bindToConcrete (x,(y,z)) $ ret . reorder
        where
            reorder (x,(y,z)) = (x,y,z)

instance ToConcrete a => ToConcrete (Arg a) where
    type ConOfAbs (Arg a) = Arg (ConOfAbs a)

    toConcrete (Arg i a) = Arg i <$> toConcreteHiding i a

    bindToConcrete (Arg info x) ret =
      bindToConcreteHiding info x $ ret . Arg info

instance ToConcrete a => ToConcrete (WithHiding a) where
  type ConOfAbs (WithHiding a) = WithHiding (ConOfAbs a)

  toConcrete     (WithHiding h a) = WithHiding h <$> toConcreteHiding h a
  bindToConcrete (WithHiding h a) ret = bindToConcreteHiding h a $ \ a ->
    ret $ WithHiding h a

instance ToConcrete a => ToConcrete (Named name a)  where
    type ConOfAbs (Named name a) = Named name (ConOfAbs a)

    toConcrete (Named n x) = Named n <$> toConcrete x
    bindToConcrete (Named n x) ret = bindToConcrete x $ ret . Named n

-- Names ------------------------------------------------------------------

instance ToConcrete A.Name where
  type ConOfAbs A.Name = C.Name

  toConcrete       = toConcreteName
  bindToConcrete x = bindName x

instance ToConcrete BindName where
  type ConOfAbs BindName = C.BoundName

  toConcrete       = fmap C.mkBoundName_ . toConcreteName . unBind
  bindToConcrete x = bindName (unBind x) . (. C.mkBoundName_)

instance ToConcrete A.QName where
  type ConOfAbs A.QName = C.QName

  toConcrete = lookupQName AmbiguousConProjs

instance ToConcrete A.ModuleName where
  type ConOfAbs A.ModuleName = C.QName
  toConcrete = lookupModule

instance ToConcrete AbstractName where
  type ConOfAbs AbstractName = C.QName
  toConcrete = toConcrete . anameName

-- | Assumes name is not 'UnknownName'.
instance ToConcrete ResolvedName where
  type ConOfAbs ResolvedName = C.QName

  toConcrete = \case
    VarName x _          -> C.QName <$> toConcrete x
    DefinedName _ x s    -> addSuffixConcrete s $ toConcrete x
    FieldName xs         -> toConcrete (List1.head xs)
    ConstructorName _ xs -> toConcrete (List1.head xs)
    PatternSynResName xs -> toConcrete (List1.head xs)
    UnknownName          -> __IMPOSSIBLE__

addSuffixConcrete :: HasOptions m => A.Suffix -> m C.QName -> m C.QName
addSuffixConcrete A.NoSuffix x = x
addSuffixConcrete (A.Suffix i) x = do
  glyphMode <- optUseUnicode <$> pragmaOptions
  addSuffixConcrete' glyphMode i <$> x

addSuffixConcrete' :: UnicodeOrAscii -> Integer -> C.QName -> C.QName
addSuffixConcrete' glyphMode i = set (C.lensQNameName . nameSuffix) suffix
  where
    suffix = Just $ case glyphMode of
      UnicodeOk -> Subscript $ fromInteger i
      AsciiOnly -> Index $ fromInteger i

-- Expression instance ----------------------------------------------------

instance ToConcrete A.Expr where
    type ConOfAbs A.Expr = C.Expr

    toConcrete (Var x)             = Ident . C.QName <$> toConcrete x
    toConcrete (Def' x suffix)     = Ident <$> addSuffixConcrete suffix (toConcrete x)
    toConcrete (Proj ProjPrefix p) = Ident <$> toConcrete (headAmbQ p)
    toConcrete (Proj _          p) = C.Dot noRange . Ident <$> toConcrete (headAmbQ p)
    toConcrete (A.Macro x)         = Ident <$> toConcrete x
    toConcrete e@(Con c)           = tryToRecoverPatternSyn e $ Ident <$> toConcrete (headAmbQ c)
        -- for names we have to use the name from the info, since the abstract
        -- name has been resolved to a fully qualified name (except for
        -- variables)
    toConcrete e@(A.Lit i (LitQName x)) = tryToRecoverPatternSyn e $ do
      x <- lookupQName AmbiguousNothing x
      let r = getRange i
      bracket appBrackets $ return $
        C.App r (C.Quote r) (defaultNamedArg $ C.Ident x)
    toConcrete e@(A.Lit i l) = tryToRecoverPatternSyn e $ return $ C.Lit (getRange i) l

    -- Andreas, 2014-05-17  We print question marks with their
    -- interaction id, in case @metaNumber /= Nothing@
    -- Ulf, 2017-09-20  ... or @preserveIIds == True@.
    toConcrete (A.QuestionMark i ii) = do
      preserve <- asks preserveIIds
      return $ C.QuestionMark (getRange i) $
                 interactionId ii <$ guard (preserve || isJust (metaNumber i))

    toConcrete (A.Underscore i) =
      C.Underscore (getRange i) <$>
      traverse (render <.> prettyTCM)
        (NamedMeta (metaNameSuggestion i) <$> metaNumber i)

    toConcrete (A.Dot i e) =
      C.Dot (getRange i) <$> toConcrete e

    toConcrete e@(A.App i e1 e2) = do
      is <- isBuiltinFun
      -- Special printing of desugared overloaded literals:
      --  fromNat 4        --> 4
      --  fromNeg 4        --> -4
      --  fromString "foo" --> "foo"
      -- Only when the corresponding conversion function is in scope and was
      -- inserted by the system.
      case (getHead e1, namedArg e2) of
        (Just (HdDef q), l@A.Lit{})
          | any (is q) [builtinFromNat, builtinFromString], visible e2,
            getOrigin i == Inserted -> toConcrete l
        (Just (HdDef q), A.Lit r (LitNat n))
          | q `is` builtinFromNeg, visible e2,
            getOrigin i == Inserted -> toConcrete (A.Lit r (LitNat (-n)))
        _ ->
          tryToRecoverPatternSyn e
          $ tryToRecoverOpApp e
          $ tryToRecoverNatural e
          -- or fallback to App
          $ bracket (appBrackets' $ preferParenless (appParens i) && isLambda e2)
          $ do e1' <- toConcreteCtx FunctionCtx e1
               e2' <- toConcreteCtx (ArgumentCtx $ appParens i) e2
               return $ C.App (getRange i) e1' e2'

    toConcrete (A.WithApp i e es) =
      bracket withAppBrackets $ do
        e <- toConcreteCtx WithFunCtx e
        es <- mapM (toConcreteCtx WithArgCtx) es
        return $ C.WithApp (getRange i) e es

    toConcrete (A.AbsurdLam i h) =
      bracket lamBrackets $ return $ C.AbsurdLam (getRange i) h
    toConcrete e@(A.Lam i _ _) =
      tryToRecoverOpApp e $   -- recover sections
        bindToConcrete (fmap makeDomainFree bs) $ \ bs' -> do
          List1.ifNull (catMaybes bs')
            {-then-} (toConcrete e')
            {-else-} $ \ bs -> bracket lamBrackets $
              C.Lam (getRange i) bs <$> toConcreteTop e'
      where
          (bs, e') = lamView e
          -- #3238 GA: We drop the hidden lambda abstractions which have
          -- been inserted by the machine rather than the user. This means
          -- that the result of lamView may actually be an empty list of
          -- binders.
          lamView :: A.Expr -> ([A.LamBinding], A.Expr)
          lamView (A.Lam _ b@(A.DomainFree _ x) e)
            | isInsertedHidden x = lamView e
            | otherwise = case lamView e of
              (bs@(A.DomainFree{} : _), e) -> (b:bs, e)
              _                            -> ([b] , e)
          lamView (A.Lam _ b@(A.DomainFull A.TLet{}) e) = case lamView e of
            (bs@(A.DomainFull _ : _), e) -> (b:bs, e)
            _                            -> ([b], e)
          lamView (A.Lam _ (A.DomainFull (A.TBind r t xs ty)) e) =
            case List1.filter (not . isInsertedHidden) xs of
              []    -> lamView e
              x:xs' -> let b = A.DomainFull (A.TBind r t (x :| xs') ty) in
                case lamView e of
                  (bs@(A.DomainFull _ : _), e) -> (b:bs, e)
                  _                            -> ([b], e)
          lamView e = ([], e)
    toConcrete (A.ExtendedLam i di erased qname cs) =
        bracket lamBrackets $ do
          decls <- concat <$> toConcrete cs
          puns  <- optHiddenArgumentPuns <$> pragmaOptions
          let -- If --hidden-argument-puns is active, then {x} is
              -- replaced by {(x)} and ⦃ x ⦄ by ⦃ (x) ⦄.
              noPun (Named Nothing p@C.IdentP{}) | puns =
                Named Nothing (C.ParenP noRange p)
              noPun p = p

              namedPat np = case getHiding np of
                 NotHidden  -> namedArg np
                 Hidden     -> C.HiddenP noRange (noPun (unArg np))
                 Instance{} -> C.InstanceP noRange (noPun (unArg np))
              -- we know all lhs are of the form `.extlam p1 p2 ... pn`,
              -- with the name .extlam leftmost. It is our mission to remove it.
          let removeApp :: C.Pattern -> AbsToCon [C.Pattern]
              removeApp (C.RawAppP _ (List2 _ p ps)) = return $ p:ps
              removeApp (C.AppP (C.IdentP _ _) np) = return [namedPat np]
              removeApp (C.AppP p np)            = removeApp p <&> (++ [namedPat np])
              -- Andreas, 2018-06-18, issue #3136
              -- Empty pattern list also allowed in extended lambda,
              -- thus, we might face the unapplied .extendedlambda identifier.
              removeApp x@C.IdentP{} = return []

              removeApp p = do
                reportSLn "extendedlambda" 50 $ "abstractToConcrete removeApp p = " ++ show p
                return [p] -- __IMPOSSIBLE__
                  -- Andreas, this is actually not impossible,
                  -- my strictification exposed this sleeping bug
          let decl2clause (C.FunClause (C.LHS p [] []) rhs C.NoWhere ca) = do
                reportSLn "extendedlambda" 50 $ "abstractToConcrete extended lambda pattern p = " ++ show p
                ps <- removeApp p
                reportSLn "extendedlambda" 50 $ "abstractToConcrete extended lambda patterns ps = " ++ prettyShow ps
                return $ LamClause ps rhs ca
              decl2clause _ = __IMPOSSIBLE__
          C.ExtendedLam (getRange i) erased . List1.fromListSafe __IMPOSSIBLE__ <$>
            mapM decl2clause decls
            -- TODO List1: can we demonstrate non-emptiness?

    toConcrete (A.Pi _ tel1 e0) = do
      let (tel, e) = piTel1 tel1 e0
      bracket piBrackets $
         bindToConcrete tel $ \ tel' ->
           C.makePi (List1.catMaybes tel') <$> toConcreteTop e
      where
        piTel1 tel e         = first (List1.appendList tel) $ piTel e
        piTel (A.Pi _ tel e) = first List1.toList $ piTel1 tel e
        piTel e              = ([], e)

    toConcrete (A.Generalized _ e) = C.Generalized <$> toConcrete e

    toConcrete (A.Fun i a b) =
        bracket piBrackets
        $ do a' <- toConcreteCtx ctx a
             b' <- toConcreteTop b
             let dom = setQuantity (getQuantity a') $ defaultArg $ addRel a' $ mkArg a'
             return $ C.Fun (getRange i) dom b'
             -- Andreas, 2018-06-14, issue #2513
             -- TODO: print attributes
        where
            ctx = if isRelevant a then FunctionSpaceDomainCtx else DotPatternCtx
            addRel a e = case getRelevance a of
                           Irrelevant -> C.Dot (getRange a) e
                           NonStrict  -> C.DoubleDot (getRange a) e
                           _          -> e
            mkArg (Arg info e) = case getHiding info of
                                          Hidden     -> HiddenArg   (getRange e) (unnamed e)
                                          Instance{} -> InstanceArg (getRange e) (unnamed e)
                                          NotHidden  -> e

    toConcrete (A.Let i ds e) =
        bracket lamBrackets
        $ bindToConcrete ds $ \ds' -> do
             e'  <- toConcreteTop e
             return $ C.mkLet (getRange i) (concat ds') e'

    toConcrete (A.Rec i fs) =
      bracket appBrackets $ do
        C.Rec (getRange i) . map (fmap (\x -> ModuleAssignment x [] defaultImportDir)) <$> toConcreteTop fs

    toConcrete (A.RecUpdate i e fs) =
      bracket appBrackets $ do
        C.RecUpdate (getRange i) <$> toConcrete e <*> toConcreteTop fs

    toConcrete (A.ScopedExpr _ e) = toConcrete e
    toConcrete (A.Quote i) = return $ C.Quote (getRange i)
    toConcrete (A.QuoteTerm i) = return $ C.QuoteTerm (getRange i)
    toConcrete (A.Unquote i) = return $ C.Unquote (getRange i)

    -- Andreas, 2012-04-02: TODO!  print DontCare as irrAxiom
    -- Andreas, 2010-10-05 print irrelevant things as ordinary things
    toConcrete (A.DontCare e) = C.Dot r . C.Paren r  <$> toConcrete e
       where r = getRange e
    toConcrete (A.PatternSyn n) = C.Ident <$> toConcrete (headAmbQ n)

makeDomainFree :: A.LamBinding -> A.LamBinding
makeDomainFree b@(A.DomainFull (A.TBind _ tac (x :| []) t)) =
  case unScope t of
    A.Underscore A.MetaInfo{metaNumber = Nothing} ->
      A.DomainFree (tbTacticAttr tac) x
    _ -> b
makeDomainFree b = b

-- Christian Sattler, 2017-08-05, fixing #2669
-- Both methods of ToConcrete (FieldAssignment' a) (FieldAssignment' c) need
-- to be implemented, each in terms of the corresponding one of ToConcrete a c.
-- This mirrors the instance ToConcrete (Arg a) (Arg c).
-- The default implementations of ToConcrete are not valid semantically.
instance ToConcrete a => ToConcrete (FieldAssignment' a) where
    type ConOfAbs (FieldAssignment' a) = FieldAssignment' (ConOfAbs a)
    toConcrete = traverse toConcrete

    bindToConcrete (FieldAssignment name a) ret =
      bindToConcrete a $ ret . FieldAssignment name


-- Binder instances -------------------------------------------------------

-- If there is no label we set it to the bound name, to make renaming the bound
-- name safe.
forceNameIfHidden :: NamedArg A.Binder -> NamedArg A.Binder
forceNameIfHidden x
  | isJust $ getNameOf  x = x
  | visible x             = x
  | otherwise             = setNameOf (Just name) x
  where
    name = WithOrigin Inserted
         $ Ranged (getRange x)
         $ C.nameToRawName $ nameConcrete
         $ unBind $ A.binderName $ namedArg x

instance ToConcrete a => ToConcrete (A.Binder' a) where
  type ConOfAbs (A.Binder' a) = C.Binder' (ConOfAbs a)

  bindToConcrete (A.Binder p a) ret =
    bindToConcrete a $ \ a ->
    bindToConcrete p $ \ p ->
    ret $ C.Binder p a

instance ToConcrete A.LamBinding where
    type ConOfAbs A.LamBinding = Maybe C.LamBinding

    bindToConcrete (A.DomainFree t x) ret = do
      t <- traverse toConcrete t
      let setTac x = x { bnameTactic = t }
      bindToConcrete (forceNameIfHidden x) $
        ret . Just . C.DomainFree . updateNamedArg (fmap setTac)
    bindToConcrete (A.DomainFull b) ret = bindToConcrete b $ ret . fmap C.DomainFull

instance ToConcrete A.TypedBinding where
    type ConOfAbs A.TypedBinding = Maybe C.TypedBinding

    bindToConcrete (A.TBind r t xs e) ret = do
        tac <- traverse toConcrete (tbTacticAttr t)
        bindToConcrete (fmap forceNameIfHidden xs) $ \ xs -> do
          e <- toConcreteTop e
          let setTac x = x { bnameTactic = tac , C.bnameIsFinite = tbFinite t }
          ret $ Just $ C.TBind r (fmap (updateNamedArg (fmap setTac)) xs) e
    bindToConcrete (A.TLet r lbs) ret =
        bindToConcrete lbs $ \ ds -> do
        ret $ C.mkTLet r $ concat ds

instance ToConcrete A.LetBinding where
    type ConOfAbs A.LetBinding = [C.Declaration]

    bindToConcrete (A.LetBind i info x t e) ret =
        bindToConcrete x $ \ x ->
        do (t, (e, [], [], [])) <- toConcrete (t, A.RHS e Nothing)
           ret $ addInstanceB (if isInstance info then Just noRange else Nothing) $
               [ C.TypeSig info Nothing (C.boundName x) t
               , C.FunClause
                   (C.LHS (C.IdentP True $ C.QName $ C.boundName x) [] [])
                   e C.NoWhere False
               ]
    -- TODO: bind variables
    bindToConcrete (LetPatBind i p e) ret = do
        p <- toConcrete p
        e <- toConcrete e
        ret [ C.FunClause (C.LHS p [] []) (C.RHS e) NoWhere False ]
    bindToConcrete (LetApply i erased x modapp _ _) ret = do
      x' <- unqualify <$> toConcrete x
      modapp <- toConcrete modapp
      let r = getRange modapp
          open = fromMaybe DontOpen $ minfoOpenShort i
          dir  = fromMaybe defaultImportDir{ importDirRange = r } $ minfoDirective i
      -- This is no use since toAbstract LetDefs is in localToAbstract.
      local (openModule' x dir id) $
        ret [ C.ModuleMacro (getRange i) erased x' modapp open dir ]
    bindToConcrete (LetOpen i x _) ret = do
      x' <- toConcrete x
      let dir = fromMaybe defaultImportDir $ minfoDirective i
      local (openModule' x dir restrictPrivate) $
            ret [ C.Open (getRange i) x' dir ]
    bindToConcrete (LetDeclaredVariable _) ret =
      -- Note that the range of the declaration site is dropped.
      ret []

instance ToConcrete A.WhereDeclarations where
  type ConOfAbs A.WhereDeclarations = WhereClause

  bindToConcrete (A.WhereDecls _ _ Nothing) ret = ret C.NoWhere
  bindToConcrete (A.WhereDecls (Just am) False
                    (Just (A.Section _ erased _ _ ds)))
                 ret = do
    ds' <- declsToConcrete ds
    cm  <- unqualify <$> lookupModule am
    -- Andreas, 2016-07-08 I put PublicAccess in the following SomeWhere
    -- Should not really matter for printing...
    let wh' = if isNoName cm && not (isErased erased)
              then AnyWhere noRange ds'
              else SomeWhere noRange erased cm PublicAccess ds'
    local (openModule' am defaultImportDir id) $ ret wh'
  bindToConcrete (A.WhereDecls _ _ (Just d)) ret =
    ret . AnyWhere noRange =<< toConcrete d

mergeSigAndDef :: [C.Declaration] -> [C.Declaration]
mergeSigAndDef (C.RecordSig _ er x bs e : C.RecordDef r y dir _ fs : ds)
  | x == y = C.Record r er y dir bs e fs : mergeSigAndDef ds
mergeSigAndDef (C.DataSig _ er x bs e : C.DataDef r y _ cs : ds)
  | x == y = C.Data r er y bs e cs : mergeSigAndDef ds
mergeSigAndDef (d : ds) = d : mergeSigAndDef ds
mergeSigAndDef [] = []

openModule' :: A.ModuleName -> C.ImportDirective -> (Scope -> Scope) -> Env -> Env
openModule' x dir restrict env = env{currentScope = set scopeModules mods' sInfo}
  where sInfo = currentScope env
        amod  = sInfo ^. scopeCurrent
        mods  = sInfo ^. scopeModules
        news  = setScopeAccess PrivateNS
                $ applyImportDirective dir
                $ maybe emptyScope restrict
                $ Map.lookup x mods
        mods' = Map.update (Just . (`mergeScope` news)) amod mods


-- Declaration instances --------------------------------------------------

declsToConcrete :: [A.Declaration] -> AbsToCon [C.Declaration]
declsToConcrete ds = mergeSigAndDef . concat <$> toConcrete ds

instance ToConcrete A.RHS where
    type ConOfAbs A.RHS = (C.RHS, [C.RewriteEqn], [C.WithExpr], [C.Declaration])

    toConcrete (A.RHS e (Just c)) = return (C.RHS c, [], [], [])
    toConcrete (A.RHS e Nothing) = do
      e <- toConcrete e
      return (C.RHS e, [], [], [])
    toConcrete A.AbsurdRHS = return (C.AbsurdRHS, [], [], [])
    toConcrete (A.WithRHS _ es cs) = do
      es <- do es <- toConcrete es
               forM es $ \ (Named n e) -> do
                 n <- traverse toConcrete n
                 pure $ Named (C.boundName <$> n) e
      cs <- noTakenNames $ concat <$> toConcrete cs
      return (C.AbsurdRHS, [], es, cs)
    toConcrete (A.RewriteRHS xeqs _spats rhs wh) = do
      wh <- maybe (return []) toConcrete $ A.whereDecls wh
      (rhs, eqs', es, whs) <- toConcrete rhs
      unless (null eqs') __IMPOSSIBLE__
      eqs <- toConcrete xeqs
      return (rhs, eqs, es, wh ++ whs)

instance (ToConcrete p, ToConcrete a) => ToConcrete (RewriteEqn' qn A.BindName p a) where
  type ConOfAbs (RewriteEqn' qn A.BindName p a) = (RewriteEqn' () C.Name (ConOfAbs p) (ConOfAbs a))

  toConcrete = \case
    Rewrite es    -> Rewrite <$> mapM (toConcrete . (\ (_, e) -> ((),e))) es
    Invert qn pes -> fmap (Invert ()) $ forM pes $ \ (Named n pe) -> do
      pe <- toConcrete pe
      n  <- toConcrete n
      pure $ Named n pe

instance ToConcrete (Maybe A.BindName) where
  type ConOfAbs (Maybe A.BindName) = Maybe C.Name
  toConcrete = traverse (C.boundName <.> toConcrete)

instance ToConcrete (Maybe A.QName) where
  type ConOfAbs (Maybe A.QName) = Maybe C.Name

  toConcrete = mapM (toConcrete . qnameName)

instance ToConcrete (Constr A.Constructor) where
  type ConOfAbs (Constr A.Constructor) = C.Declaration

  toConcrete (Constr (A.ScopedDecl scope [d])) =
    withScope scope $ toConcrete (Constr d)
  toConcrete (Constr (A.Axiom _ i info Nothing x t)) = do
    x' <- unsafeQNameToName <$> toConcrete x
    t' <- toConcreteTop t
    return $ C.TypeSig info Nothing x' t'
  toConcrete (Constr (A.Axiom _ _ _ (Just _) _ _)) = __IMPOSSIBLE__
  toConcrete (Constr d) = head <$> toConcrete d

instance (ToConcrete a, ConOfAbs a ~ C.LHS) => ToConcrete (A.Clause' a) where
  type ConOfAbs (A.Clause' a) = [C.Declaration]

  toConcrete (A.Clause lhs _ rhs wh catchall) =
      bindToConcrete lhs $ \case
          C.LHS p _ _ -> do
            bindToConcrete wh $ \ wh' -> do
                (rhs', eqs, with, wcs) <- toConcreteTop rhs
                return $ FunClause (C.LHS p eqs with) rhs' wh' catchall : wcs

instance ToConcrete A.ModuleApplication where
  type ConOfAbs A.ModuleApplication = C.ModuleApplication

  toConcrete (A.SectionApp tel y es) = do
    y  <- toConcreteCtx FunctionCtx y
    bindToConcrete tel $ \ tel -> do
      es <- toConcreteCtx argumentCtx_ es
      let r = fuseRange y es
      return $ C.SectionApp r (catMaybes tel) (foldl (C.App r) (C.Ident y) es)

  toConcrete (A.RecordModuleInstance recm) = do
    recm <- toConcrete recm
    return $ C.RecordModuleInstance (getRange recm) recm

instance ToConcrete A.Declaration where
  type ConOfAbs A.Declaration = [C.Declaration]

  toConcrete (ScopedDecl scope ds) =
    withScope scope (declsToConcrete ds)

  toConcrete (A.Axiom _ i info mp x t) = do
    x' <- unsafeQNameToName <$> toConcrete x
    withAbstractPrivate i $
      withInfixDecl i x'  $ do
      t' <- toConcreteTop t
      return $
        (case mp of
           Nothing   -> []
           Just occs -> [C.Pragma (PolarityPragma noRange x' occs)]) ++
        [C.Postulate (getRange i) [C.TypeSig info Nothing x' t']]

  toConcrete (A.Generalize s i j x t) = do
    x' <- unsafeQNameToName <$> toConcrete x
    tac <- traverse toConcrete (defTactic i)
    withAbstractPrivate i $
      withInfixDecl i x'  $ do
      t' <- toConcreteTop t
      return [C.Generalize (getRange i) [C.TypeSig j tac x' $ C.Generalized t']]

  toConcrete (A.Field i x t) = do
    x' <- unsafeQNameToName <$> toConcrete x
    tac <- traverse toConcrete (defTactic i)
    withAbstractPrivate i $
      withInfixDecl i x'  $ do
      t' <- toConcreteTop t
      return [C.FieldSig (A.defInstance i) tac x' t']

  toConcrete (A.Primitive i x t) = do
    x' <- unsafeQNameToName <$> toConcrete x
    withAbstractPrivate i $
      withInfixDecl i x'  $ do
      t' <- traverse toConcreteTop t
      return [C.Primitive (getRange i) [C.TypeSig (argInfo t') Nothing x' (unArg t')]]
        -- Primitives are always relevant.

  toConcrete (A.FunDef i _ _ cs) =
    withAbstractPrivate i $ concat <$> toConcrete cs

  toConcrete (A.DataSig i erased x bs t) =
    withAbstractPrivate i $
    bindToConcrete (A.generalizeTel bs) $ \ tel' -> do
      x' <- unsafeQNameToName <$> toConcrete x
      t' <- toConcreteTop t
      return [ C.DataSig (getRange i) erased x'
                 (map C.DomainFull $ catMaybes tel') t' ]

  toConcrete (A.DataDef i x uc bs cs) =
    withAbstractPrivate i $
    bindToConcrete (map makeDomainFree $ dataDefParams bs) $ \ tel' -> do
      (x',cs') <- first unsafeQNameToName <$> toConcrete (x, map Constr cs)
      return [ C.DataDef (getRange i) x' (catMaybes tel') cs' ]

  toConcrete (A.RecSig i erased x bs t) =
    withAbstractPrivate i $
    bindToConcrete (A.generalizeTel bs) $ \ tel' -> do
      x' <- unsafeQNameToName <$> toConcrete x
      t' <- toConcreteTop t
      return [ C.RecordSig (getRange i) erased x'
                 (map C.DomainFull $ catMaybes tel') t' ]

  toConcrete (A.RecDef  i x uc dir bs t cs) =
    withAbstractPrivate i $
    bindToConcrete (map makeDomainFree $ dataDefParams bs) $ \ tel' -> do
      (x',cs') <- first unsafeQNameToName <$> toConcrete (x, map Constr cs)
      return [ C.RecordDef (getRange i) x' (dir { recConstructor = Nothing }) (catMaybes tel') cs' ]

  toConcrete (A.Mutual i ds) = pure . C.Mutual noRange <$> declsToConcrete ds

  toConcrete (A.Section i erased x (A.GeneralizeTel _ tel) ds) = do
    x <- toConcrete x
    bindToConcrete tel $ \ tel -> do
      ds <- declsToConcrete ds
      return [ C.Module (getRange i) erased x (catMaybes tel) ds ]

  toConcrete (A.Apply i erased x modapp _ _) = do
    x  <- unsafeQNameToName <$> toConcrete x
    modapp <- toConcrete modapp
    let r = getRange modapp
        open = fromMaybe DontOpen $ minfoOpenShort i
        dir  = fromMaybe defaultImportDir{ importDirRange = r } $ minfoDirective i
    return [ C.ModuleMacro (getRange i) erased x modapp open dir ]

  toConcrete (A.Import i x _) = do
    x <- toConcrete x
    let open = fromMaybe DontOpen $ minfoOpenShort i
        dir  = fromMaybe defaultImportDir $ minfoDirective i
    return [ C.Import (getRange i) x Nothing open dir]

  toConcrete (A.Pragma i p)     = do
    p <- toConcrete $ RangeAndPragma (getRange i) p
    return [C.Pragma p]

  toConcrete (A.Open i x _) = do
    x <- toConcrete x
    return [C.Open (getRange i) x defaultImportDir]

  toConcrete (A.PatternSynDef x xs p) = do
    C.QName x <- toConcrete x
    bindToConcrete (map (fmap A.unBind) xs) $ \ xs ->
      singleton . C.PatternSyn (getRange x) x xs <$> do
        dontFoldPatternSynonyms $ toConcrete (vacuous p :: A.Pattern)

  toConcrete (A.UnquoteDecl _ i xs e) = do
    let unqual (C.QName x) = return x
        unqual _           = __IMPOSSIBLE__
    xs <- mapM (unqual <=< toConcrete) xs
    (:[]) . C.UnquoteDecl (getRange i) xs <$> toConcrete e

  toConcrete (A.UnquoteDef i xs e) = do
    let unqual (C.QName x) = return x
        unqual _           = __IMPOSSIBLE__
    xs <- mapM (unqual <=< toConcrete) xs
    (:[]) . C.UnquoteDef (getRange i) xs <$> toConcrete e

  toConcrete (A.UnquoteData i xs uc j cs e) = __IMPOSSIBLE__
  toConcrete (A.UnfoldingDecl r ns) = __IMPOSSIBLE__

data RangeAndPragma = RangeAndPragma Range A.Pragma

instance ToConcrete RangeAndPragma where
  type ConOfAbs RangeAndPragma = C.Pragma

  toConcrete (RangeAndPragma r p) = case p of
    A.OptionsPragma xs  -> return $ C.OptionsPragma r xs
    A.BuiltinPragma b x       -> C.BuiltinPragma r b <$> toConcrete x
    A.BuiltinNoDefPragma b _kind x -> C.BuiltinPragma r b <$> toConcrete x
    A.RewritePragma r' x      -> C.RewritePragma r r' <$> toConcrete x
    A.CompilePragma b x s -> do
      x <- toConcrete x
      return $ C.CompilePragma r b x s
    A.StaticPragma x -> C.StaticPragma r <$> toConcrete x
    A.InjectivePragma x -> C.InjectivePragma r <$> toConcrete x
    A.InlinePragma b x -> C.InlinePragma r b <$> toConcrete x
    A.NotProjectionLikePragma q -> C.NotProjectionLikePragma r <$> toConcrete q
    A.EtaPragma x    -> C.EtaPragma    r <$> toConcrete x
    A.DisplayPragma f ps rhs ->
      C.DisplayPragma r <$> toConcrete (A.DefP (PatRange noRange) (unambiguous f) ps) <*> toConcrete rhs

-- Left hand sides --------------------------------------------------------

instance ToConcrete A.SpineLHS where
  type ConOfAbs A.SpineLHS = C.LHS

  bindToConcrete lhs = bindToConcrete (A.spineToLhs lhs :: A.LHS)

instance ToConcrete A.LHS where
    type ConOfAbs A.LHS = C.LHS

    bindToConcrete (A.LHS i lhscore) ret = do
      bindToConcreteCtx TopCtx lhscore $ \ lhs ->
          ret $ C.LHS (reintroduceEllipsis (lhsEllipsis i) lhs) [] []

instance ToConcrete A.LHSCore where
  type ConOfAbs A.LHSCore = C.Pattern
  bindToConcrete = bindToConcrete . lhsCoreToPattern

appBracketsArgs :: [arg] -> PrecedenceStack -> Bool
appBracketsArgs []    _   = False
appBracketsArgs (_:_) ctx = appBrackets ctx

-- Auxiliary wrappers for processing the bindings in patterns in the right order.
newtype UserPattern a  = UserPattern a
newtype SplitPattern a = SplitPattern a
newtype BindingPattern = BindingPat A.Pattern
newtype FreshenName = FreshenName BindName

instance ToConcrete FreshenName where
  type ConOfAbs FreshenName = A.Name
  bindToConcrete (FreshenName BindName{ unBind = x }) ret = bindToConcrete x $ \ y -> ret x { nameConcrete = y }

-- Pass 1: (Issue #2729)
-- Takes care of binding the originally user-written pattern variables, but doesn't actually
-- translate anything to Concrete.
instance ToConcrete (UserPattern A.Pattern) where
  type ConOfAbs (UserPattern A.Pattern) = A.Pattern

  bindToConcrete (UserPattern p) ret = do
    reportSLn "toConcrete.pat" 100 $ "binding pattern (pass 1)" ++ show p
    case p of
      A.VarP bx -> do
        let x = unBind bx
        case isInScope x of
          InScope            -> bindName' x $ ret $ A.VarP bx
          C.NotInScope       -> bindName x $ \y ->
                                ret $ A.VarP $ mkBindName $ x { nameConcrete = y }
      A.WildP{}              -> ret p
      A.ProjP{}              -> ret p
      A.AbsurdP{}            -> ret p
      A.LitP{}               -> ret p
      A.DotP{}               -> ret p
      A.EqualP{}             -> ret p
      -- Andreas, 2017-09-03, issue #2729:
      -- Do not go into patterns generated by case-split here!
      -- They are treated in a second pass.
      A.ConP i c args
        | conPatOrigin i == ConOSplit -> ret p
        | otherwise          -> bindToConcrete (map UserPattern args) $ ret . A.ConP i c
      A.DefP i f args        -> bindToConcrete (map UserPattern args) $ ret . A.DefP i f
      A.PatternSynP i f args -> bindToConcrete (map UserPattern args) $ ret . A.PatternSynP i f
      A.RecP i args          -> bindToConcrete ((map . fmap) UserPattern args) $ ret . A.RecP i
      A.AsP i x p            -> bindName' (unBind x) $
                                bindToConcrete (UserPattern p) $ \ p ->
                                ret (A.AsP i x p)
      A.WithP i p            -> bindToConcrete (UserPattern p) $ ret . A.WithP i
      A.AnnP i a p           -> bindToConcrete (UserPattern p) $ ret . A.AnnP i a

instance ToConcrete (UserPattern (NamedArg A.Pattern)) where
  type ConOfAbs (UserPattern (NamedArg A.Pattern)) = NamedArg A.Pattern

  bindToConcrete (UserPattern np) ret =
    case getOrigin np of
      CaseSplit -> ret np
      _         -> bindToConcrete (fmap (fmap UserPattern) np) ret

-- Pass 2a: locate case-split pattern.  Don't bind anything!
instance ToConcrete (SplitPattern A.Pattern) where
  type ConOfAbs (SplitPattern A.Pattern) = A.Pattern

  bindToConcrete (SplitPattern p) ret = do
    reportSLn "toConcrete.pat" 100 $ "binding pattern (pass 2a)" ++ show p
    case p of
      A.VarP x               -> ret p
      A.WildP{}              -> ret p
      A.ProjP{}              -> ret p
      A.AbsurdP{}            -> ret p
      A.LitP{}               -> ret p
      A.DotP{}               -> ret p
      A.EqualP{}             -> ret p
      -- Andreas, 2017-09-03, issue #2729:
      -- For patterns generated by case-split here, switch to freshening & binding.
      A.ConP i c args
        | conPatOrigin i == ConOSplit
                             -> bindToConcrete ((map . fmap . fmap) BindingPat args) $ ret . A.ConP i c
        | otherwise          -> bindToConcrete (map SplitPattern args) $ ret . A.ConP i c
      A.DefP i f args        -> bindToConcrete (map SplitPattern args) $ ret . A.DefP i f
      A.PatternSynP i f args -> bindToConcrete (map SplitPattern args) $ ret . A.PatternSynP i f
      A.RecP i args          -> bindToConcrete ((map . fmap) SplitPattern args) $ ret . A.RecP i
      A.AsP i x p            -> bindToConcrete (SplitPattern p)  $ \ p ->
                                ret (A.AsP i x p)
      A.WithP i p            -> bindToConcrete (SplitPattern p) $ ret . A.WithP i
      A.AnnP i a p           -> bindToConcrete (SplitPattern p) $ ret . A.AnnP i a

instance ToConcrete (SplitPattern (NamedArg A.Pattern)) where
  type ConOfAbs (SplitPattern (NamedArg A.Pattern)) = NamedArg A.Pattern
  bindToConcrete (SplitPattern np) ret =
    case getOrigin np of
      CaseSplit -> bindToConcrete (fmap (fmap BindingPat  ) np) ret
      _         -> bindToConcrete (fmap (fmap SplitPattern) np) ret


-- Pass 2b:
-- Takes care of freshening and binding pattern variables introduced by case split.
-- Still does not translate anything to Concrete.
instance ToConcrete BindingPattern where
  type ConOfAbs BindingPattern = A.Pattern
  bindToConcrete (BindingPat p) ret = do
    reportSLn "toConcrete.pat" 100 $ "binding pattern (pass 2b)" ++ show p
    case p of
      A.VarP x               -> bindToConcrete (FreshenName x) $ ret . A.VarP . mkBindName
      A.WildP{}              -> ret p
      A.ProjP{}              -> ret p
      A.AbsurdP{}            -> ret p
      A.LitP{}               -> ret p
      A.DotP{}               -> ret p
      A.EqualP{}             -> ret p
      A.ConP i c args        -> bindToConcrete (map (updateNamedArg BindingPat) args) $ ret . A.ConP i c
      A.DefP i f args        -> bindToConcrete (map (updateNamedArg BindingPat) args) $ ret . A.DefP i f
      A.PatternSynP i f args -> bindToConcrete (map (updateNamedArg BindingPat) args) $ ret . A.PatternSynP i f
      A.RecP i args          -> bindToConcrete ((map . fmap)        BindingPat args) $ ret . A.RecP i
      A.AsP i x p            -> bindToConcrete (FreshenName x) $ \ x ->
                                bindToConcrete (BindingPat p)  $ \ p ->
                                ret (A.AsP i (mkBindName x) p)
      A.WithP i p            -> bindToConcrete (BindingPat p) $ ret . A.WithP i
      A.AnnP i a p           -> bindToConcrete (BindingPat p) $ ret . A.AnnP i a

instance ToConcrete A.Pattern where
  type ConOfAbs A.Pattern = C.Pattern

  bindToConcrete p ret = do
    prec <- currentPrecedence
    bindToConcrete (UserPattern p) $ \ p -> do
      bindToConcrete (SplitPattern p) $ \ p -> do
        ret =<< do withPrecedence' prec $ toConcrete p
  toConcrete p =
    case p of
      A.VarP x ->
        C.IdentP True . C.QName . C.boundName <$> toConcrete x

      A.WildP i ->
        return $ C.WildP (getRange i)

      A.ConP i c args  -> tryOp (headAmbQ c) (A.ConP i c) args

      A.ProjP i ProjPrefix p -> C.IdentP True <$> toConcrete (headAmbQ p)
      A.ProjP i _          p -> C.DotP noRange . C.Ident <$> toConcrete (headAmbQ p)

      A.DefP i x args -> tryOp (headAmbQ x) (A.DefP i x)  args

      A.AsP i x p -> do
        (x, p) <- toConcreteCtx argumentCtx_ (x, p)
        return $ C.AsP (getRange i) (C.boundName x) p

      A.AbsurdP i ->
        return $ C.AbsurdP (getRange i)

      A.LitP i (LitQName x) -> do
        x <- lookupQName AmbiguousNothing x
        bracketP_ appBrackets $ return $
          C.AppP (C.QuoteP (getRange i))
            (defaultNamedArg (C.IdentP True x))
      A.LitP i l ->
        return $ C.LitP (getRange i) l

      -- Andreas, 2018-06-19, issue #3130
      -- Print .p as .(p) if p is a projection
      -- to avoid confusion with projection pattern.
      A.DotP i e@A.Proj{} -> C.DotP r . C.Paren r <$> toConcreteCtx TopCtx e
        where r = getRange i

      -- gallais, 2019-02-12, issue #3491
      -- Print p as .(p) if p is a variable but there is a projection of the
      -- same name in scope.
      A.DotP i e@(A.Var v) -> do
        let r = getRange i
        -- Erase @v@ to a concrete name and resolve it back to check whether
        -- we have a conflicting field name.
        cn <- toConcreteName v
        resolveName (someKindsOfNames [FldName]) Nothing (C.QName cn) >>= \ case
          -- If we do then we print .(v) rather than .v
          Right FieldName{} -> do
            reportSLn "print.dotted" 50 $ "Wrapping ambiguous name " ++ prettyShow (nameConcrete v)
            C.DotP r . C.Paren r <$> toConcrete (A.Var v)
          Right _ -> printDotDefault i e
          Left _ -> __IMPOSSIBLE__

      A.DotP i e -> printDotDefault i e

      A.EqualP i es -> do
        C.EqualP (getRange i) <$> toConcrete es

      A.PatternSynP i n args -> tryOp (headAmbQ n) (A.PatternSynP i n) args

      A.RecP i as ->
        C.RecP (getRange i) <$> mapM (traverse toConcrete) as

      A.WithP i p -> C.WithP (getRange i) <$> toConcreteCtx WithArgCtx p

      A.AnnP i a p -> toConcrete p -- TODO: print type annotation

    where

    printDotDefault :: PatInfo -> A.Expr -> AbsToCon C.Pattern
    printDotDefault i e = do
      c <- toConcreteCtx DotPatternCtx e
      let r = getRange i
      case c of
        -- Andreas, 2016-02-04 print ._ pattern as _ pattern,
        -- following the fusing of WildP and ImplicitP.
        C.Underscore{} -> return $ C.WildP r
        _ -> return $ C.DotP r c

    tryOp :: A.QName -> (A.Patterns -> A.Pattern) -> A.Patterns -> AbsToCon C.Pattern
    tryOp x f args = do
      -- Andreas, 2016-02-04, Issue #1792
      -- To prevent failing of tryToRecoverOpAppP for overapplied operators,
      -- we take off the exceeding arguments first
      -- and apply them pointwise with C.AppP later.
      let (args1, args2) = splitAt (numHoles x) args
      let funCtx = applyUnless (null args2) (withPrecedence FunctionCtx)
      tryToRecoverPatternSynP (f args) $ funCtx (tryToRecoverOpAppP $ f args1) >>= \case
        Just c  -> applyTo args2 c
        Nothing -> applyTo args . C.IdentP True =<< toConcrete x
    -- Note: applyTo [] c = return c
    applyTo args c = bracketP_ (appBracketsArgs args) $ do
      foldl C.AppP c <$>
        (mapM avoidPun =<< toConcreteCtx argumentCtx_ args)

    -- If --hidden-argument-puns is active, then {x} is replaced by
    -- {(x)} and ⦃ x ⦄ by ⦃ (x) ⦄.
    avoidPun :: NamedArg C.Pattern -> AbsToCon (NamedArg C.Pattern)
    avoidPun arg =
      ifM (optHiddenArgumentPuns <$> pragmaOptions)
          (return $ case arg of
             Arg i (Named Nothing x@C.IdentP{}) | notVisible i ->
               Arg i (Named Nothing (C.ParenP noRange x))
             arg -> arg)
          (return arg)

instance ToConcrete (Maybe A.Pattern) where
  type ConOfAbs (Maybe A.Pattern) = Maybe C.Pattern

  toConcrete = traverse toConcrete

-- Helpers for recovering natural number literals

tryToRecoverNatural :: A.Expr -> AbsToCon C.Expr -> AbsToCon C.Expr
tryToRecoverNatural e def = do
  is <- isBuiltinFun
  caseMaybe (recoverNatural is e) def $ return . C.Lit noRange . LitNat

recoverNatural :: (A.QName -> BuiltinId -> Bool) -> A.Expr -> Maybe Integer
recoverNatural is e = explore (`is` builtinZero) (`is` builtinSuc) 0 e
  where
    explore :: (A.QName -> Bool) -> (A.QName -> Bool) -> Integer -> A.Expr -> Maybe Integer
    explore isZero isSuc k (A.App _ (A.Con c) t) | Just f <- getUnambiguous c, isSuc f
                                                = (explore isZero isSuc $! k + 1) (namedArg t)
    explore isZero isSuc k (A.Con c) | Just x <- getUnambiguous c, isZero x = Just k
    explore isZero isSuc k (A.Lit _ (LitNat l)) = Just (k + l)
    explore _ _ _ _                             = Nothing

-- Helpers for recovering C.OpApp ------------------------------------------

data Hd = HdVar A.Name | HdCon A.QName | HdDef A.QName | HdSyn A.QName

data MaybeSection a
  = YesSection
  | NoSection a
  deriving (Eq, Show, Functor, Foldable, Traversable)

fromNoSection :: a -> MaybeSection a -> a
fromNoSection fallback = \case
  YesSection  -> fallback
  NoSection x -> x

instance HasRange a => HasRange (MaybeSection a) where
  getRange = \case
    YesSection  -> noRange
    NoSection a -> getRange a

getHead :: A.Expr -> Maybe Hd
getHead (Var x)          = Just (HdVar x)
getHead (Def f)          = Just (HdDef f)
getHead (Proj o f)       = Just (HdDef $ headAmbQ f)
getHead (Con c)          = Just (HdCon $ headAmbQ c)
getHead (A.PatternSyn n) = Just (HdSyn $ headAmbQ n)
getHead _                = Nothing

cOpApp :: Range -> C.QName -> A.Name -> List1 (MaybeSection C.Expr) -> C.Expr
cOpApp r x n es =
  C.OpApp r x (Set.singleton n) $
  fmap (defaultNamedArg . placeholder) $
  List1.toList eps
  where
    x0 = C.unqualify x
    positions | isPrefix  x0 =              (const Middle <$> List1.drop 1 es) `List1.snoc` End
              | isPostfix x0 = Beginning :| (const Middle <$> List1.drop 1 es)
              | isInfix x0   = Beginning :| (const Middle <$> List1.drop 2 es) ++ [ End ]
              | otherwise    =               const Middle <$> es
    eps = List1.zip es positions
    placeholder (YesSection , pos ) = Placeholder pos
    placeholder (NoSection e, _pos) = noPlaceholder (Ordinary e)

tryToRecoverOpApp :: A.Expr -> AbsToCon C.Expr -> AbsToCon C.Expr
tryToRecoverOpApp e def = fromMaybeM def $
  recoverOpApp bracket (isLambda . defaultNamedArg) cOpApp view e
  where
    view :: A.Expr -> Maybe (Hd, [NamedArg (MaybeSection (AppInfo, A.Expr))])
    view e
        -- Do we have a series of inserted lambdas?
      | Just xs@(_:_) <- traverse insertedName bs =
        (,) <$> getHead hd <*> sectionArgs (map (unBind . A.binderName) xs) args
      where
        LamView     bs body = A.lamView e
        Application hd args = A.appView' body

        -- Only inserted domain-free visible lambdas come from sections.
        insertedName (A.DomainFree _ x)
          | getOrigin x == Inserted && visible x = Just $ namedArg x
        insertedName _ = Nothing

        -- Build section arguments. Need to check that:
        -- lambda bound variables appear in the right order and only as
        -- top-level arguments.
        sectionArgs :: [A.Name] -> [NamedArg (AppInfo, A.Expr)] -> Maybe [NamedArg (MaybeSection (AppInfo, A.Expr))]
        sectionArgs xs = go xs
          where
            noXs = getAll . foldExpr (\ case A.Var x -> All (x `notElem` xs)
                                             _       -> All True) . snd . namedArg
            go [] [] = return []
            go (y : ys) (arg : args)
              | visible arg
              , A.Var y' <- snd $ namedArg arg
              , y == y' = (fmap (YesSection <$) arg :) <$> go ys args
            go ys (arg : args)
              | visible arg, noXs arg = ((fmap . fmap) NoSection arg :) <$> go ys args
            go _ _ = Nothing

    view e = (, (map . fmap . fmap) NoSection args) <$> getHead hd
      where Application hd args = A.appView' e

tryToRecoverOpAppP :: A.Pattern -> AbsToCon (Maybe C.Pattern)
tryToRecoverOpAppP p = do
  res <- recoverOpApp bracketP_ (const False) opApp view p
  reportS "print.op" 90
    [ "tryToRecoverOpApp"
    , "in:  " ++ show p
    , "out: " ++ show res
    ]
  return res
  where
    opApp r x n ps = C.OpAppP r x (Set.singleton n) $
      fmap (defaultNamedArg . fromNoSection __IMPOSSIBLE__) $
      -- `view` does not generate any `Nothing`s
      List1.toList ps

    appInfo = defaultAppInfo_

    view :: A.Pattern -> Maybe (Hd, [NamedArg (MaybeSection (AppInfo, A.Pattern))])
    view = \case
      ConP _        cs ps -> Just (HdCon (headAmbQ cs), (map . fmap . fmap) (NoSection . (appInfo,)) ps)
      DefP _        fs ps -> Just (HdDef (headAmbQ fs), (map . fmap . fmap) (NoSection . (appInfo,)) ps)
      PatternSynP _ ns ps -> Just (HdSyn (headAmbQ ns), (map . fmap . fmap) (NoSection . (appInfo,)) ps)
      _                   -> Nothing
      -- ProjP _ _ d   -> Just (HdDef (headAmbQ d), [])   -- ? Andreas, 2016-04-21

recoverOpApp :: forall a c . (ToConcrete a, c ~ ConOfAbs a, HasRange c)
  => ((PrecedenceStack -> Bool) -> AbsToCon c -> AbsToCon c)
  -> (a -> Bool)  -- ^ Check for lambdas
  -> (Range -> C.QName -> A.Name -> List1 (MaybeSection c) -> c)  -- ^ @opApp@
  -> (a -> Maybe (Hd, [NamedArg (MaybeSection (AppInfo, a))]))
  -> a
  -> AbsToCon (Maybe c)
recoverOpApp bracket isLam opApp view e = case view e of
  Nothing -> mDefault
  Just (hd, args)
    | all visible args    -> do
      let  args' = map namedArg args
      case hd of
        HdVar  n
          | isNoName n    -> mDefault
          | otherwise     -> doQNameHelper (Left n) args'
        HdDef qn
          | isExtendedLambdaName qn
                          -> mDefault
          | otherwise     -> doQNameHelper (Right qn) args'
        -- HdDef qn          -> doQNameHelper (Right qn) args'
        HdCon qn          -> doQNameHelper (Right qn) args'
        HdSyn qn          -> doQNameHelper (Right qn) args'
    | otherwise           -> mDefault
  where
  mDefault = return Nothing

  skipParens :: MaybeSection (AppInfo, a) -> Bool
  skipParens = \case
     YesSection       -> False
     NoSection (i, e) -> isLam e && preferParenless (appParens i)

  doQNameHelper :: Either A.Name A.QName -> [MaybeSection (AppInfo, a)] -> AbsToCon (Maybe c)
  doQNameHelper n args = do
    x <- either (C.QName <.> toConcrete) toConcrete n
    let n' = either id A.qnameName n
    -- #1346: The fixity of the abstract name is not necessarily correct, it depends on which
    -- concrete name we choose! Make sure to resolve ambiguities with n'.
    fx <- resolveName_ x [n'] <&> \ case
            VarName y _                -> y ^. lensFixity
            DefinedName _ q _          -> q ^. lensFixity
            FieldName (q :| _)         -> q ^. lensFixity
            ConstructorName _ (q :| _) -> q ^. lensFixity
            PatternSynResName (q :| _) -> q ^. lensFixity
            UnknownName                -> noFixity
    List1.ifNull args {-then-} mDefault {-else-} $ \ as ->
      doQName fx x n' as (C.nameParts $ C.unqualify x)

  doQName :: Fixity -> C.QName -> A.Name -> List1 (MaybeSection (AppInfo, a)) -> NameParts -> AbsToCon (Maybe c)

  -- fall-back (wrong number of arguments or no holes)
  doQName _ x _ as xs
    | length as /= numHoles x = mDefault

  -- binary case
  doQName fixity x n (a1 :| as) xs
    | Hole <- List1.head xs
    , Hole <- List1.last xs = do
        let (as', an) = List1.ifNull as {-then-} __IMPOSSIBLE__ {-else-} List1.initLast
        Just <$> do
          bracket (opBrackets' (skipParens an) fixity) $ do
            e1 <- traverse (toConcreteCtx (LeftOperandCtx fixity) . snd) a1
            es <- (mapM . traverse) (toConcreteCtx InsideOperandCtx . snd) as'
            en <- traverse (uncurry $ toConcreteCtx . RightOperandCtx fixity . appParens) an
            return $ opApp (getRange (e1, en)) x n (e1 :| es ++ [en])

  -- prefix
  doQName fixity x n as xs
    | Hole <- List1.last xs = do
        let (as', an) = List1.initLast as
        Just <$> do
          bracket (opBrackets' (skipParens an) fixity) $ do
            es <- (mapM . traverse) (toConcreteCtx InsideOperandCtx . snd) as'
            en <- traverse (\ (i, e) -> toConcreteCtx (RightOperandCtx fixity $ appParens i) e) an
            return $ opApp (getRange (n, en)) x n (List1.snoc es en)

  -- postfix
  doQName fixity x n as xs
    | Hole <- List1.head xs = do
        let a1  = List1.head as
            as' = List1.tail as
        e1 <- traverse (toConcreteCtx (LeftOperandCtx fixity) . snd) a1
        es <- (mapM . traverse) (toConcreteCtx InsideOperandCtx . snd) as'
        Just <$> do
          bracket (opBrackets fixity) $
            return $ opApp (getRange (e1, n)) x n (e1 :| es)

  -- roundfix
  doQName _ x n as _ = do
    es <- (mapM . traverse) (toConcreteCtx InsideOperandCtx . snd) as
    Just <$> do
      bracket roundFixBrackets $
        return $ opApp (getRange x) x n es

-- Recovering pattern synonyms --------------------------------------------

-- | Recover pattern synonyms for expressions.
tryToRecoverPatternSyn :: A.Expr -> AbsToCon C.Expr -> AbsToCon C.Expr
tryToRecoverPatternSyn e fallback
  | userWritten e = fallback
  | litOrCon e    = recoverPatternSyn apply matchPatternSyn e fallback
  | otherwise     = fallback
  where
    userWritten (A.App info _ _) = getOrigin info == UserWritten
    userWritten _                = False  -- this means we always use pattern synonyms for nullary constructors

    -- Only literals or constructors can head pattern synonym definitions
    litOrCon e =
      case A.appView e of
        Application Con{}   _ -> True
        Application A.Lit{} _ -> True
        _                     -> False

    apply c args = A.unAppView $ Application (A.PatternSyn $ unambiguous c) args

-- | Recover pattern synonyms in patterns.
tryToRecoverPatternSynP :: A.Pattern -> AbsToCon C.Pattern -> AbsToCon C.Pattern
tryToRecoverPatternSynP = recoverPatternSyn apply matchPatternSynP
  where apply c args = PatternSynP patNoRange (unambiguous c) args

-- | General pattern synonym recovery parameterised over expression type
recoverPatternSyn :: ToConcrete a =>
  (A.QName -> [NamedArg a] -> a)         -> -- applySyn
  (PatternSynDefn -> a -> Maybe [Arg a]) -> -- match
  a -> AbsToCon (ConOfAbs a) -> AbsToCon (ConOfAbs a)
recoverPatternSyn applySyn match e fallback = do
  doFold <- asks foldPatternSynonyms
  if not doFold then fallback else do
    psyns  <- getAllPatternSyns
    scope  <- getScope
    reportSLn "toConcrete.patsyn" 100 $ render $ hsep $
      [ "Scope when attempting to recover pattern synonyms:"
      , pretty scope
      ]
    let isConP ConP{} = True    -- #2828: only fold pattern synonyms with
        isConP _      = False   --        constructor rhs
        cands = [ (q, args, score rhs)
                | (q, psyndef@(_, rhs)) <- reverse $ Map.toList psyns
                , isConP rhs
                , Just args <- [match psyndef e]
                -- #3879: only fold pattern synonyms with an unqualified concrete name in scope
                -- Note that we only need to consider the head of the inverse lookup result: they
                -- are already sorted from shortest to longest!
                , C.QName{} <- Fold.toList $ listToMaybe $ inverseScopeLookupName q scope
                ]
        cmp (_, _, x) (_, _, y) = compare y x
    reportSLn "toConcrete.patsyn" 50 $ render $ hsep $
      [ "Found pattern synonym candidates:"
      , prettyList_ $ map (\ (q,_,_) -> q) cands
      ]
    case sortBy cmp cands of
      (q, args, _) : _ -> toConcrete $ applySyn q $ (map . fmap) unnamed args
      []               -> fallback
  where
    -- Heuristic to pick the best pattern synonym: the one that folds the most
    -- constructors.
    score :: Pattern' Void -> Int
    score = getSum . foldAPattern con
      where con ConP{} = 1
            con _      = 0

-- Some instances that are related to interaction with users -----------

instance ToConcrete InteractionId where
    type ConOfAbs InteractionId = C.Expr
    toConcrete (InteractionId i) = return $ C.QuestionMark noRange (Just i)

instance ToConcrete NamedMeta where
    type ConOfAbs NamedMeta = C.Expr
    toConcrete i =
      C.Underscore noRange . Just . render <$> prettyTCM i
