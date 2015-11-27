{-# LANGUAGE CPP                        #-}
{-# LANGUAGE DeriveDataTypeable         #-}
{-# LANGUAGE DeriveFoldable             #-}
{-# LANGUAGE DeriveFunctor              #-}
{-# LANGUAGE DeriveTraversable          #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE PatternGuards              #-}
{-# LANGUAGE TupleSections              #-}
{-# LANGUAGE UndecidableInstances       #-}
{-# LANGUAGE StandaloneDeriving         #-}

module Agda.TypeChecking.Rules.LHS.Unify where

import Prelude hiding (null)

import Control.Arrow ((***))
import Control.Applicative hiding (empty)
import Control.Monad
import Control.Monad.State
import Control.Monad.Reader
import Control.Monad.Writer (WriterT(..), MonadWriter(..), Monoid(..))

import Data.IntMap (IntMap)
import qualified Data.IntMap as IntMap
import Data.Map (Map)
import qualified Data.Map as Map
import Data.List hiding (null, sort)

import Data.Typeable (Typeable)
import Data.Foldable (Foldable)
import Data.Traversable (Traversable,traverse)

import Agda.Interaction.Options (optInjectiveTypeConstructors)

import Agda.Syntax.Common
import Agda.Syntax.Internal as I hiding (Substitution)
import Agda.Syntax.Literal
import Agda.Syntax.Position

import Agda.TypeChecking.Monad
import qualified Agda.TypeChecking.Monad.Benchmark as Bench
import Agda.TypeChecking.Monad.Exception
import Agda.TypeChecking.Monad.Builtin (constructorForm)
import Agda.TypeChecking.Conversion -- equalTerm
import Agda.TypeChecking.Constraints
import Agda.TypeChecking.Datatypes
import Agda.TypeChecking.DropArgs
import Agda.TypeChecking.Level (reallyUnLevelView)
import Agda.TypeChecking.Reduce
import Agda.TypeChecking.Pretty
import Agda.TypeChecking.Substitute hiding (Substitution)
import qualified Agda.TypeChecking.Substitute as S
import Agda.TypeChecking.Telescope
import Agda.TypeChecking.Free
import Agda.TypeChecking.Records
import Agda.TypeChecking.MetaVars (assignV, newArgsMetaCtx)
import Agda.TypeChecking.EtaContract
import Agda.Interaction.Options (optInjectiveTypeConstructors, optWithoutK)

import Agda.TypeChecking.Rules.LHS.Problem
-- import Agda.TypeChecking.SyntacticEquality

import Agda.Utils.Except
  ( Error(noMsg, strMsg)
  , MonadError(catchError, throwError)
  )
import Agda.Utils.Either
import Agda.Utils.List
import Agda.Utils.Maybe
import Agda.Utils.Monad
import Agda.Utils.Null
import Agda.Utils.Size

#include "undefined.h"
import Agda.Utils.Impossible

-- | Result of 'unifyIndices'.
type UnificationResult = UnificationResult' Substitution

data UnificationResult' a
  = Unifies  a      -- ^ Unification succeeded.
  | NoUnify  TCErr  -- ^ Terms are not unifiable.
  | DontKnow TCErr  -- ^ Some other error happened, unification got stuck.
  deriving (Typeable, Show, Functor, Foldable, Traversable)

-- | Monad for unification.
newtype Unify a = U { unUnify ::
  ReaderT UnifyEnv (
  WriterT UnifyOutput (
  ExceptionT UnifyException (
  StateT UnifyState TCM))) a
  } deriving ( Monad, MonadIO, Functor, Applicative
             , MonadException UnifyException, MonadWriter UnifyOutput)

instance MonadTCM Unify where
  liftTCM = U . lift . lift . lift . lift

instance MonadState TCState Unify where
  get = liftTCM $ get
  put = liftTCM . put

instance MonadReader TCEnv Unify where
  ask = U $ ReaderT $ \ _ -> ask
  local cont (U (ReaderT f)) = U $ ReaderT $ \ a -> local cont (f a)

instance HasConstInfo Unify where
  getConstInfo       = U . lift . lift . lift . lift . getConstInfo
  getRewriteRulesFor = U . lift . lift . lift . lift . getRewriteRulesFor

-- UnifyEnv
------------------------------------------------------------------------

data UnifyMayPostpone = MayPostpone | MayNotPostpone

type UnifyEnv = UnifyMayPostpone

emptyUEnv :: UnifyEnv
emptyUEnv = MayPostpone

noPostponing :: Unify a -> Unify a
noPostponing = U . local (const MayNotPostpone) . unUnify

askPostpone :: Unify UnifyMayPostpone
askPostpone = U $ ask

-- | Output the result of unification (success or maybe).
type UnifyOutput = Unifiable

-- | Were two terms unifiable or did we have to postpone some equation such that we are not sure?
data Unifiable
  = Definitely  -- ^ Unification succeeded.
  | Possibly    -- ^ Unification did not fail, but we had to postpone a part.

-- | Conjunctive monoid.
instance Monoid Unifiable where
  mempty = Definitely
  mappend Definitely Definitely = Definitely
  mappend _ _ = Possibly

-- | Tell that something could not be unified right now,
--   so the unification succeeds only 'Possibly'.
reportPostponing :: Unify ()
reportPostponing = tell Possibly

-- | Check whether unification proceeded without postponement.
ifClean :: Unify () -> Unify a -> Unify a -> Unify a
ifClean m t e = do
  ok <- snd <$> listen m
  case ok of
    Definitely -> t
    Possibly ->   e

data Equality = Equal TypeHH Term Term
type Sub = IntMap Term

data UnifyException
  = ConstructorMismatch Type Term Term
  | StronglyRigidOccurrence Type Term Term
  | UnclearOccurrence Type Term Term
  | WithoutKException Type Term Term
  | GenericUnifyException String

instance Error UnifyException where
  strMsg = GenericUnifyException

data UnifyState = USt
  { uniSub    :: Sub
  , uniConstr :: [Equality]
  }

emptyUState :: UnifyState
emptyUState = USt IntMap.empty []

-- | Throw-away error message.
projectionMismatch :: QName -> QName -> Unify a
projectionMismatch f f' = throwException $ GenericUnifyException $
  "projections " ++ show f ++ " and " ++ show f' ++ " do not match"

constructorMismatch :: Type -> Term -> Term -> Unify a
constructorMismatch a u v = throwException $ ConstructorMismatch a u v

constructorMismatchHH :: TypeHH -> Term -> Term -> Unify a
constructorMismatchHH aHH u v = do
  ifM (liftTCM fullyApplied `and2M` canCompare aHH)
    {- then -} (constructorMismatch (leftHH aHH) u v) -- do not report heterogenity
    {- else -} (throwException (UnclearOccurrence (leftHH aHH) u v))
  where
    -- Comparing constructors at different types is incompatible with univalence
    canCompare (Het s t) = ifM (liftTCM $ optWithoutK <$> pragmaOptions)
                               (liftTCM $ tryConversion $ equalType s t)  -- no constraints left
                               (return True)
    canCompare Hom{} = return True
    -- Issue 1497: only fully applied constructors can mismatch
    fullyApplied = case (ignoreSharing u, ignoreSharing v) of
      (Con c us, Con d vs) -> do
        when (c == d) __IMPOSSIBLE__
        car <- getConstructorArity (conName c)
        dar <- getConstructorArity (conName d)
        return $ length us == car && length vs == dar
      _ -> return True  -- could be literals

instance Subst Term Equality where
  applySubst rho (Equal a s t) =
    Equal (applySubst rho a) (applySubst rho s) (applySubst rho t)

getSub :: Unify Sub
getSub = U $ gets uniSub

modSub :: (Sub -> Sub) -> Unify ()
modSub f = U $ modify $ \s -> s { uniSub = f $ uniSub s }

checkEqualities :: [Equality] -> TCM ()
checkEqualities eqs = noConstraints $ mapM_ checkEq eqs
  where
    checkEq (Equal (Hom a) s t) =
      ifM ((optWithoutK <$> pragmaOptions) `and2M` (not <$> isSet (unEl a)))
      {-then-} (typeError $ WithoutKError a s t)
      {-else-} (equalTerm a s t)
    checkEq (Equal (Het a1 a2) s t) = typeError $ HeterogeneousEquality s a1 t a2
    -- Andreas, 2014-03-03:  Alternatively, one could try to get back
    -- to a homogeneous situation.  Unless there is a case where this
    -- actually helps, I leave it deactivated.
    -- KEEP:
    --
    -- checkEq (Equal (Het a1 a2) s t) = do
    --     noConstraints $ do
    --       equalType a1 a2
    --       equalTerm a1 s t
    --   `catchError` \ _ -> typeError $ HeterogeneousEquality s a1 t a2

-- | Force equality now instead of postponing it using 'addEquality'.
checkEquality :: Type -> Term -> Term -> TCM ()
checkEquality a u v = noConstraints $ equalTerm a u v

-- | Try equality.  If constraints remain, postpone (enter unsafe mode).
--   Heterogeneous equalities cannot be tried nor reawakened,
--   so we can throw them away and flag "dirty".
checkEqualityHH :: TypeHH -> Term -> Term -> Unify ()
checkEqualityHH (Hom a) u v = do
    ok <- liftTCM $ tryConversion $ equalTerm a u v  -- no constraints left
    -- Jesper, 2013-11-21: Refuse to solve reflexive equations when --without-K is enabled
    if ok
      then (whenM (liftTCM $ (optWithoutK <$> pragmaOptions) `and2M` (not <$> isSet (unEl a)))
           (throwException $ WithoutKException a u v))
      else (addEquality a u v)
checkEqualityHH aHH@(Het a1 a2) u v = -- reportPostponing -- enter "dirty" mode
    addEqualityHH aHH u v -- postpone, enter "dirty" mode

-- | Check whether heterogeneous situation is really homogeneous.
--   If not, give up.
forceHom :: TypeHH -> TCM Type
forceHom (Hom a)     = return a
forceHom (Het a1 a2) = a1 <$ do noConstraints $ equalType a1 a2

-- | Check whether heterogeneous situation is really homogeneous.
--   If not, return Nothing.
makeHom :: TypeHH -> TCM (Maybe Type)
makeHom aHH = (Just <$> forceHom aHH) `catchError` \ err -> return Nothing

-- | Try to make a possibly heterogeneous term situation homogeneous.
tryHom :: TypeHH -> Term -> Term -> TCM TermHH
tryHom aHH u v = do
     a <- forceHom aHH
     Hom u <$ checkEquality a u v
   `catchError` \ err -> return $ Het u v

addEquality :: Type -> Term -> Term -> Unify ()
addEquality a = addEqualityHH (Hom a)

addEqualityHH :: TypeHH -> Term -> Term -> Unify ()
addEqualityHH aHH u v = do
  reportPostponing
  U $ modify $ \s -> s { uniConstr = Equal aHH u v : uniConstr s }

takeEqualities :: Unify [Equality]
takeEqualities = U $ do
  s <- get
  put $ s { uniConstr = [] }
  return $ uniConstr s

-- | Includes flexible occurrences, metas need to be solved. TODO: relax?
--   TODO: later solutions may remove flexible occurences
occursCheck :: Nat -> Term -> Type -> Unify ()
occursCheck i u a = do
  let v  = var i
  case occurrence i u of
    -- Andreas, 2011-04-14
    -- a strongly rigid recursive occurrences signals unsolvability
    StronglyRigid -> do
      liftTCM $ reportSDoc "tc.lhs.unify" 20 $ prettyTCM v <+> text "occurs strongly rigidly in" <+> prettyTCM u
      throwException $ StronglyRigidOccurrence a v u

    NoOccurrence  -> return ()  -- this includes irrelevant occurrences!

    -- any other recursive occurrence leads to unclear situation
    _             -> do
      liftTCM $ reportSDoc "tc.lhs.unify" 20 $ prettyTCM v <+> text "occurs in" <+> prettyTCM u
      throwException $ UnclearOccurrence a v u

-- | Assignment with preceding occurs check.
(|->) :: Nat -> (Term, Type) -> Unify ()
i |-> (u, a) = do
  occursCheck i u a
  liftTCM $ reportSDoc "tc.lhs.unify.assign" 10 $ prettyTCM (var i) <+> text ":=" <+> prettyTCM u
  modSub $ IntMap.insert i (killRange u)
  -- Apply substitution to itself (issue 552)
  rho  <- getSub
  rho' <- traverse ureduce rho
  modSub $ const rho'

makeSubstitution :: Sub -> S.Substitution
makeSubstitution sub
  | null sub  = idS
  | otherwise = map val [0 .. highestIndex] ++# raiseS (highestIndex + 1)
  where
    highestIndex = fst $ IntMap.findMax sub
    val i = fromMaybe (var i) $ IntMap.lookup i sub

-- | Apply the current substitution on a term and reduce to weak head normal form.
class UReduce t where
  ureduce :: t -> Unify t

instance UReduce Term where
  ureduce u = doEtaContractImplicit $ do
    rho <- makeSubstitution <$> getSub
-- Andreas, 2013-10-24 the following call to 'normalise' is problematic
-- (see issue 924).  Instead, we only normalize if unifyAtomHH is undecided.
--    liftTCM $ etaContract =<< normalise (applySubst rho u)
-- Andreas, 2011-06-22, fix related to issue 423
-- To make eta contraction work better, I switched reduce to normalise.
-- I hope the performance penalty is not big (since we are dealing with
-- l.h.s. terms only).
-- A systematic solution would make unification type-directed and
-- eta-insensitive...
    liftTCM $ etaContract =<< reduce (applySubst rho u)

instance UReduce Type where
  ureduce (El s t) = El s <$> ureduce t

instance UReduce t => UReduce (HomHet t) where
  ureduce (Hom t)     = Hom <$> ureduce t
  ureduce (Het t1 t2) = Het <$> ureduce t1 <*> ureduce t2

-- Andreas, 2014-03-03 A variant of ureduce that tries to get back
-- to a homogeneous situation by checking syntactic equality.
-- Did not solve issue 1071, so I am reverting to the old ureduce.
-- However, KEEP THIS as an alternative to reconsider.
-- Remember to import TypeChecking.SyntacticEquality!
--
-- instance (SynEq t, UReduce t) => UReduce (HomHet t) where
--   ureduce (Hom t)     = Hom <$> ureduce t
--   ureduce (Het t1 t2) = do
--     t1 <- ureduce t1
--     t2 <- ureduce t2
--     ((t1,t2),equal) <- liftTCM $ checkSyntacticEquality t1 t2
--     -- BRITTLE: syntactic equality only
--     return $ if equal then Hom t1 else Het t1 t2

instance UReduce t => UReduce (Maybe t) where
  ureduce Nothing = return Nothing
  ureduce (Just t) = Just <$> ureduce t

instance (UReduce a, UReduce b) => UReduce (a, b) where
  ureduce (a, b) = (,) <$> ureduce a <*> ureduce b

instance (UReduce a, UReduce b, UReduce c) => UReduce (a, b, c) where
  ureduce (a, b, c) = (\x y z -> (x, y, z)) <$> ureduce a <*> ureduce b <*> ureduce c

instance (UReduce a) => UReduce (Arg a) where
  ureduce (Arg c e) = Arg c <$> ureduce e

instance (UReduce a) => UReduce [ a ] where
  ureduce = sequence . (map ureduce)


-- | Take a substitution σ and ensure that no variables from the domain appear
--   in the targets. The context of the targets is not changed.
--   TODO: can this be expressed using makeSubstitution and applySubst?
flattenSubstitution :: Substitution -> Substitution
flattenSubstitution s = foldr instantiate s is
  where
    -- instantiated variables
    is = [ i | (i, Just _) <- zip [0..] s ]

    instantiate :: Nat -> Substitution -> Substitution
    instantiate i s = map (fmap $ inst i u) s
      where
        u = case s !!! i of
              Just (Just u) -> u
              _             -> __IMPOSSIBLE__

    -- @inst i u v@ replaces index @i@ in @v@ by @u@, without removing the index.
    inst :: Nat -> Term -> Term -> Term
    inst i u v = applySubst us v
      where us = [ var j | j <- [0..i - 1] ] ++# consS u (raiseS $ i + 1)

-- | Are we in a homogeneous (one type) or heterogeneous (two types) situation?
data HomHet a
  = Hom a    -- ^ homogeneous
  | Het a a  -- ^ heterogeneous
  deriving (Typeable, Show, Eq, Ord, Functor, Foldable, Traversable)

isHom :: HomHet a -> Bool
isHom Hom{} = True
isHom Het{} = False

fromHom :: HomHet a -> a
fromHom (Hom a) = a
fromHom (Het{}) = __IMPOSSIBLE__

leftHH :: HomHet a -> a
leftHH (Hom a) = a
leftHH (Het a1 a2) = a1

rightHH :: HomHet a -> a
rightHH (Hom a) = a
rightHH (Het a1 a2) = a2

instance (Subst t a) => Subst t (HomHet a) where
  applySubst rho u = fmap (applySubst rho) u

instance (PrettyTCM a) => PrettyTCM (HomHet a) where
  prettyTCM (Hom a) = prettyTCM a
  prettyTCM (Het a1 a2) = prettyTCM a1 <+> text "||" <+> prettyTCM a2

type TermHH    = HomHet Term
type TypeHH    = HomHet Type
--type FunViewHH = FunV TypeHH
type TelHH     = Tele (Dom TypeHH)
type TelViewHH = TelV TypeHH
type ArgsHH    = HomHet Args

absAppHH :: SubstHH t tHH => Abs t -> TermHH -> tHH
absAppHH (Abs   _ t) u = substHH u t
absAppHH (NoAbs _ t) u = trivialHH t

class ApplyHH t where
  applyHH :: t -> HomHet Args -> HomHet t

instance ApplyHH Term where
  applyHH t = fmap (apply t)

instance ApplyHH Type where
  applyHH t = fmap (apply t)

substHH :: SubstHH t tHH => TermHH -> t -> tHH
substHH = substUnderHH 0

-- | @substHH u t@ substitutes @u@ for the 0th variable in @t@.
class SubstHH t tHH where
  substUnderHH :: Nat -> TermHH -> t -> tHH
  trivialHH    :: t -> tHH

instance (Free a, Subst Term a) => SubstHH (HomHet a) (HomHet a) where
  substUnderHH n (Hom u) t = fmap (substUnder n u) t
  substUnderHH n (Het u1 u2) (Hom t) =
    if n `relevantIn` t then Het (substUnder n u1 t) (substUnder n u2 t)
     else Hom (substUnder n u1 t)
  substUnderHH n (Het u1 u2) (Het t1 t2) = Het (substUnder n u1 t1) (substUnder n u2 t2)
  trivialHH = id

instance SubstHH Term (HomHet Term) where
  substUnderHH n uHH t = fmap (\ u -> substUnder n u t) uHH
  trivialHH = Hom

instance SubstHH Type (HomHet Type) where
  substUnderHH n uHH (El s t) = fmap (\ u -> El s $ substUnder n u t) uHH
-- fmap $ fmap (\ (El s v) -> El s $ substUnderHH n u v)
  -- we ignore sorts in substitution, since they do not contain
  -- terms we can match on
  trivialHH = Hom

instance SubstHH a b => SubstHH (Arg a) (Arg b) where
  substUnderHH n u = fmap $ substUnderHH n u
  trivialHH = fmap trivialHH

instance SubstHH a b => SubstHH (Dom a) (Dom b) where
  substUnderHH n u = fmap $ substUnderHH n u
  trivialHH = fmap trivialHH

instance SubstHH a b => SubstHH (Abs a) (Abs b) where
  substUnderHH n u (Abs   x v) = Abs x $ substUnderHH (n + 1) u v
  substUnderHH n u (NoAbs x v) = NoAbs x $ substUnderHH n u v
  trivialHH = fmap trivialHH

instance (SubstHH a a', SubstHH b b') => SubstHH (a,b) (a',b') where
    substUnderHH n u (x,y) = (substUnderHH n u x, substUnderHH n u y)
    trivialHH = trivialHH *** trivialHH

instance SubstHH a b => SubstHH (Tele a) (Tele b) where
  substUnderHH n u  EmptyTel         = EmptyTel
  substUnderHH n u (ExtendTel t tel) = uncurry ExtendTel $ substUnderHH n u (t, tel)
  trivialHH = fmap trivialHH

-- | Unify indices.
--
--   In @unifyIndices_ flex a us vs@,
--
--   @a@ is the type eliminated by @us@ and @vs@
--     (usally the type of a constructor),
--     need not be reduced,
--
--   @us@ and @vs@ are the argument lists to unify,
--
--   @flex@ is the set of flexible (instantiable) variabes in @us@ and @vs@.
--
--   The result is the most general unifier of @us@ and @vs@.
unifyIndices_ :: MonadTCM tcm => FlexibleVars -> Type -> Args -> Args -> tcm Substitution
unifyIndices_ flex a us vs = liftTCM $ do
  r <- unifyIndices flex a us vs
  case r of
    Unifies sub   -> return sub
    DontKnow err  -> throwError err
    NoUnify  err  -> throwError err

unifyIndices :: MonadTCM tcm => FlexibleVars -> Type -> Args -> Args -> tcm UnificationResult
unifyIndices flex a us vs = liftTCM $ Bench.billTo [Bench.Typing, Bench.CheckLHS, Bench.UnifyIndices] $ do
    a <- reduce a
    reportSDoc "tc.lhs.unify" 10 $
      sep [ text "unifyIndices"
          , nest 2 $ text (show flex)
          , nest 2 $ parens (prettyTCM a)
          , nest 2 $ prettyList $ map prettyTCM us
          , nest 2 $ prettyList $ map prettyTCM vs
          , nest 2 $ text "context: " <+> (prettyTCM =<< getContextTelescope)
          ]
    (r, USt s eqs) <- flip runStateT emptyUState . runExceptionT . runWriterT . flip runReaderT emptyUEnv . unUnify $ do
        ifClean (unifyConstructorArgs (Hom a) us vs)
          -- clean: continue unifying
          recheckConstraints
          -- dirty: just check equalities to trigger error message
          recheckEqualities

    case r of
      Left (ConstructorMismatch     a u v)  -> noUnify a u v
      -- Andreas 2011-04-14:
      Left (StronglyRigidOccurrence a u v)  -> noUnify a u v
      Left (UnclearOccurrence a u v)        -> typeError $ UnequalTerms CmpEq u v a
      Left (WithoutKException       a u v)  -> typeError $ WithoutKError a u v
      Left (GenericUnifyException     err)  -> typeError $ GenericError err
      Right _                               -> do
        checkEqualities $ applySubst (makeSubstitution s) eqs
        let n = maximum $ (-1) : flex'
        return $ Unifies $ flattenSubstitution [ IntMap.lookup i s | i <- [0..n] ]
  `catchError` \err -> case err of
     TypeError _ (Closure {clValue = WithoutKError{}}) -> throwError err
     _                                                 -> return $ DontKnow err
  where
    noUnify a u v = NoUnify <$> do typeError_ $ UnequalTerms CmpEq u v a

    flex'      = map flexVar flex
    flexible i = i `elem` flex'
    findFlexible i = find ((i ==) . flexVar) flex
    flexibleHid  i = fmap getHiding $ findFlexible i

    flexibleTerm (Var i []) = flexible i
    flexibleTerm (Shared p) = flexibleTerm (derefPtr p)
    flexibleTerm _          = False

    {- Andreas, 2011-09-12
       We unify constructors in heterogeneous situations, as long
       as the two types have the same shape (construct the same datatype).
     -}

    unifyConstructorArgs ::
         TypeHH  -- ^ The ureduced type of the constructor, instantiated to the parameters.
                 --   Possibly heterogeneous, since pars of lhs and rhs might differ.
      -> [Arg Term]  -- ^ the arguments of the constructor (lhs)
      -> [Arg Term]  -- ^ the arguments of the constructor (rhs)
      -> Unify ()
    unifyConstructorArgs a12 [] [] = return ()
    unifyConstructorArgs a12 vs1 vs2 = do
      liftTCM $ reportSDoc "tc.lhs.unify" 15 $ sep
        [ text "unifyConstructorArgs"
        -- , nest 2 $ parens (prettyTCM tel0)
        , nest 2 $ prettyList $ map prettyTCM vs1
        , nest 2 $ prettyList $ map prettyTCM vs2
        , nest 2 $ text "constructor type:" <+> prettyTCM a12
        ]
      let n = genericLength vs1
      -- since c vs1 and c vs2 have same-shaped type
      -- vs1 and vs2 must have same length
      when (n /= genericLength vs2) $ __IMPOSSIBLE__
      TelV tel12 _ <- telViewUpToHH n a12
      -- if the length of tel12 is not n, then something is wrong
      -- e.g. a12 is not a same-shaped pair of types
      when (n /= size tel12) $ __IMPOSSIBLE__
      unifyConArgs tel12 vs1 vs2

    unifyConArgs ::
         TelHH  -- ^ The telescope(s) of the constructor args [length = n].
      -> Args   -- ^ the arguments of the constructor (lhs)   [length = n].
      -> Args   -- ^ the arguments of the constructor (rhs)   [length = n].
      -> Unify ()
    unifyConArgs _ (_ : _) [] = __IMPOSSIBLE__
    unifyConArgs _ [] (_ : _) = __IMPOSSIBLE__
    unifyConArgs _ []      [] = return ()
    unifyConArgs EmptyTel _ _ = __IMPOSSIBLE__
    unifyConArgs tel0@(ExtendTel a@(Dom _ bHH) tel) us0@(arg@(Arg _ u) : us) vs0@(Arg _ v : vs) = do
      liftTCM $ reportSDoc "tc.lhs.unify" 15 $ sep
        [ text "unifyConArgs"
        -- , nest 2 $ parens (prettyTCM tel0)
        , nest 2 $ prettyList $ map prettyTCM us0
        , nest 2 $ prettyList $ map prettyTCM vs0
        , nest 2 $ text "at telescope" <+> prettyTCM bHH <+> text ("(" ++ show (getRelevance a) ++ ") ...")
        ]
      liftTCM $ reportSDoc "tc.lhs.unify" 25 $
        (text $ "tel0 = " ++ show tel0)


      -- Andreas, Ulf, 2011-09-08 (AIM XIV)
      -- in case of dependent function type, we cannot postpone
      -- unification of u and v, otherwise us or vs might be ill-typed
      -- skip irrelevant parts
      uHH <- if getRelevance a == Irrelevant then return $ Hom u else
             -- Andreas, 2015-01-19 Forced constructor arguments are not unified.
             -- Andreas, 2015-02-26 Restricting this to big forced arguments;
             -- this still addresses issue 1406.
             if getRelevance a == Forced Big then liftTCM $ tryHom bHH u v else
               ifClean (unifyHH bHH u v) (return $ Hom u) (return $ Het u v)

      liftTCM $ reportSDoc "tc.lhs.unify" 25 $
        (text "uHH (before ureduce) =" <+> prettyTCM uHH)

      uHH <- traverse ureduce uHH

      liftTCM $ reportSDoc "tc.lhs.unify" 25 $
        (text "uHH (after  ureduce) =" <+> prettyTCM uHH)

      unifyConArgs (tel `absAppHH` uHH) us vs

    -- | Used for arguments of a 'Def' (data/record/postulate), not 'Con'.
    unifyArgs :: Type -> [Arg Term] -> [Arg Term] -> Unify ()
    unifyArgs _ (_ : _) [] = __IMPOSSIBLE__
    unifyArgs _ [] (_ : _) = __IMPOSSIBLE__
    unifyArgs _ [] [] = return ()
    unifyArgs a us0@(arg@(Arg _ u) : us) vs0@(Arg _ v : vs) = do
      liftTCM $ reportSDoc "tc.lhs.unify" 15 $ sep
        [ text "unifyArgs"
        , nest 2 $ parens (prettyTCM a)
        , nest 2 $ prettyList $ map prettyTCM us0
        , nest 2 $ prettyList $ map prettyTCM vs0
        ]
      a <- ureduce a  -- Q: reduce sufficient?
      case ignoreSharing $ unEl a of
        Pi b _  -> do
          -- Andreas, Ulf, 2011-09-08 (AIM XVI)
          -- in case of dependent function type, we cannot postpone
          -- unification of u and v, otherwise us or vs might be ill-typed
          let dep = dependent $ unEl a
          -- skip irrelevant parts
          unless (isIrrelevant b) $
            (if dep then noPostponing else id) $
              unify (unDom b) u v
          arg <- traverse ureduce arg
          unifyArgs (a `piApply` [arg]) us vs
        _         -> __IMPOSSIBLE__
      where dependent (Pi _ NoAbs{}) = False
            dependent (Pi b c)       = 0 `relevantIn` absBody c
            dependent (Shared p)     = dependent (derefPtr p)
            dependent _              = False

    -- | Check using conversion check.
    recheckEqualities :: Unify ()
    recheckEqualities = do
      eqs <- takeEqualities
      liftTCM $ checkEqualities eqs

    -- | Check using unifier.
    recheckConstraints :: Unify ()
    recheckConstraints = mapM_ unifyEquality =<< takeEqualities

    unifyEquality :: Equality -> Unify ()
    unifyEquality (Equal aHH u v) = unifyHH aHH u v

    i |->> x = do
      i |-> x
      recheckConstraints

    maybeAssign h i x = (i |->> x) `catchException` \e ->
      case e of
        UnclearOccurrence{} -> h
        _                   -> throwException e

    unifySizes :: Term -> Term -> Unify ()
    unifySizes u v = do
      sz <- liftTCM sizeType
      su <- liftTCM $ sizeView u
      sv <- liftTCM $ sizeView v
      case (su, sv) of
        (SizeSuc u, SizeSuc v) -> unify sz u v
        (SizeSuc u, SizeInf) -> unify sz u v
        (SizeInf, SizeSuc v) -> unify sz u v
        _                    -> unifyAtomHH (Hom sz) u v checkEqualityHH

    -- | Possibly heterogeneous unification (but at same-shaped types).
    --   In het. situations, we only search for a mismatch!
    --
    -- TODO: eta for records!
    unifyHH ::
        TypeHH  -- ^ one or two types, need not be in (u)reduced form
     -> Term -> Term -> Unify ()
    unifyHH aHH u v = do
      liftTCM $ reportSDoc "tc.lhs.unify" 15 $
        sep [ text "unifyHH"
            , nest 2 $ (parens $ prettyTCM u) <+> text "=?="
            , nest 2 $ parens $ prettyTCM v
            , nest 2 $ text ":" <+> prettyTCM aHH
            ]
      u <- liftTCM . constructorForm =<< ureduce u
      v <- liftTCM . constructorForm =<< ureduce v
      aHH <- ureduce aHH
      liftTCM $ reportSDoc "tc.lhs.unify" 25 $
        sep [ text "unifyHH (reduced)"
            , nest 2 $ (parens $ prettyTCM u) <+> text "=?="
            , nest 2 $ parens $ prettyTCM v
            , nest 2 $ text ":" <+> prettyTCM aHH
            ]
      -- obtain the (== Size) function
      isSizeName <- liftTCM isSizeNameTest

      -- Andreas, 2013-10-24 (fixing issue 924)
      -- Only if we cannot make progress, we try full normalization!
      let tryAgain aHH u v = do
            u <- liftTCM $ etaContract =<< normalise u
            v <- liftTCM $ etaContract =<< normalise v
            unifyAtomHH aHH u v $ \ aHH u v -> do
              -- Andreas, 2014-03-03 (issue 1061)
              -- As a last resort, normalize types to maybe get back
              -- to the homogeneous case
              caseMaybeM (liftTCM $ makeHom aHH) (checkEqualityHH aHH u v) $ \ a -> do
                unifyAtomHH (Hom a) u v checkEqualityHH

      -- check whether types have the same shape
      (aHH, sh) <- shapeViewHH aHH
      case sh of
        ElseSh  -> checkEqualityHH aHH u v -- not a type or not same types

        DefSh d | isSizeName d -> unifySizes u v

        _ -> unifyAtomHH aHH u v tryAgain

    unifyAtomHH ::
         TypeHH -- ^ in ureduced form
      -> Term
      -> Term
      -> (TypeHH -> Term -> Term -> Unify ())
         -- ^ continuation in case unification was inconclusive
      -> Unify ()
    unifyAtomHH aHH0 u v tryAgain = do
      let (aHH, homogeneous, a) = case aHH0 of
            Hom a                -> (aHH0, True, a)
            Het a1 a2 | a1 == a2 -> (Hom a1, True, a1) -- BRITTLE: just checking syn.eq.
            _                    -> (aHH0, False, __IMPOSSIBLE__)
           -- use @a@ only if 'homogeneous' holds!

          fallback = tryAgain aHH u v
                   -- Try again if occurs check fails non-rigidly. It might be
                   -- that normalising gets rid of the occurrence.
          (|->?) = maybeAssign fallback

      -- If one side is a literal and the other not, we convert the literal to
      -- constructor form.
      let isLit u = case ignoreSharing u of Lit{} -> True; _ -> False
      (u, v) <- liftTCM $ if isLit u /= isLit v
                then (,) <$> constructorForm u <*> constructorForm v
                else return (u, v)

      liftTCM $ reportSDoc "tc.lhs.unify" 15 $
        sep [ text "unifyAtom"
            , nest 2 $ prettyTCM u <> if flexibleTerm u then text " (flexible)" else empty
            , nest 2 $ text "=?="
            , nest 2 $ prettyTCM v <> if flexibleTerm v then text " (flexible)" else empty
            , nest 2 $ text ":" <+> prettyTCM aHH
            ]
      liftTCM $ reportSDoc "tc.lhs.unify" 60 $
        text $ "aHH = " ++ show aHH
      case (ignoreSharing u, ignoreSharing v) of
        -- Ulf, 2011-06-19
        -- We don't want to worry about levels here.
        (Level l, _) -> do
            u <- liftTCM $ reallyUnLevelView l
            unifyAtomHH aHH u v tryAgain
        (_, Level l) -> do
            v <- liftTCM $ reallyUnLevelView l
            unifyAtomHH aHH u v tryAgain
        (Var i us, Var j vs) | i == j  -> checkEqualityHH aHH u v
-- Andreas, 2013-03-05: the following flex/flex case is an attempt at
-- better dotting (see Issue811).  Does not work perfectly, maybe the best choice
-- which variable to assign cannot made locally, but would need a look at the full
-- picture!?  Or maybe the information on flexible variables in not yet good enough
-- in the call to split in Coverage.
        (Var i [], Var j []) | homogeneous, Just fi <- findFlexible i, Just fj <- findFlexible j -> do
            liftTCM $ reportSDoc "tc.lhs.unify.flexflex" 20 $
              sep [ text "unifying flexible/flexible"
                  , nest 2 $ text "i =" <+> prettyTCM u <+> text ("; fi = " ++ show fi)
                  , nest 2 $ text "j =" <+> prettyTCM v <+> text ("; fj = " ++ show fj)
                  ]
            -- We assign the "bigger" variable, where dotted, hidden, earlier is bigger
            -- (in this order, see Problem.hs).
            -- The comparison is total.
            if fj >= fi then j |->? (u, a) else i |->? (v, a)
        (Var i [], _) | homogeneous && flexible i -> i |->? (v, a)
        (_, Var j []) | homogeneous && flexible j -> j |->? (u, a)
        (Con c us, Con c' vs)
          | c == c' -> do
              r <- liftTCM (dataOrRecordTypeHH' c aHH)
              case r of
                Just (d, b, parsIxsHH) -> do
                  (b, parsIxsHH) <- ureduce (b, parsIxsHH)
                  -- Jesper, 2014-05-03: When --without-K is enabled, we reconstruct
                  -- datatype indices and unify them as well
                  withoutKEnabled <- liftTCM $ optWithoutK <$> pragmaOptions
                  when withoutKEnabled $ do
                      def   <- liftTCM $ getConstInfo d
                      let parsHH  = fst <$> parsIxsHH
                          ixsHH   = snd <$> parsIxsHH
                          dtypeHH = defType def `applyHH` parsHH
                      unifyConstructorArgs dtypeHH (leftHH ixsHH) (rightHH ixsHH)
                  let a'HH = (b `apply`) . fst <$> parsIxsHH
                  unifyConstructorArgs a'HH us vs
                Nothing -> checkEqualityHH aHH u v
          | otherwise -> constructorMismatchHH aHH u v
        -- Definitions are ok as long as they can't reduce (i.e. datatypes/axioms)
        (Def d es, Def d' es')
          | d == d' -> do
              -- d must be a data, record or axiom
              def <- getConstInfo d
              let ok = case theDef def of
                    Datatype{} -> True
                    Record{}   -> True
                    Axiom{}    -> True
                    _          -> False
              inj <- liftTCM $ optInjectiveTypeConstructors <$> pragmaOptions
              if inj && ok then do
                  let us = fromMaybe __IMPOSSIBLE__ $ allApplyElims es
                      vs = fromMaybe __IMPOSSIBLE__ $ allApplyElims es'
                  unifyArgs (defType def) us vs `catchException` \ _ ->
                       constructorMismatchHH aHH u v
                else checkEqualityHH aHH u v
          -- Andreas, 2011-05-30: if heads disagree, abort
          -- but do not raise "mismatch" because otherwise type constructors
          -- would be distinct
          | otherwise -> checkEqualityHH aHH u v -- typeError $ UnequalTerms CmpEq u v a
        (Lit l1, Lit l2)
          | l1 == l2  -> return ()
          | otherwise -> constructorMismatchHH aHH u v

        -- We can instantiate metas if the other term is inert (constructor application)
        -- Andreas, 2011-09-13: test/succeed/IndexInference needs this feature.
        (MetaV m us, _) | homogeneous -> do
            ok <- liftTCM $ instMetaE a m us v
            liftTCM $ reportSDoc "tc.lhs.unify" 40 $
              vcat [ fsep [ text "inst meta", text $ if ok then "(ok)" else "(not ok)" ]
                   , nest 2 $ sep [ prettyTCM u, text ":=", prettyTCM =<< normalise u ]
                   ]
            if ok then unify a u v
                  else addEquality a u v
        (_, MetaV m vs) | homogeneous -> do
            ok <- liftTCM $ instMetaE a m vs u
            liftTCM $ reportSDoc "tc.lhs.unify" 40 $
              vcat [ fsep [ text "inst meta", text $ if ok then "(ok)" else "(not ok)" ]
                   , nest 2 $ sep [ prettyTCM v, text ":=", prettyTCM =<< normalise v ]
                   ]
            if ok then unify a u v
                  else addEquality a u v

        (Con c us, _) -> do
           md <- isEtaRecordTypeHH aHH
           case md of
             Just (d, parsHH) -> do
               (tel, vs) <- liftTCM $ etaExpandRecord d (rightHH parsHH) v
               b <- liftTCM $ getRecordConstructorType d
               bHH <- ureduce (b `applyHH` parsHH)
               unifyConstructorArgs bHH us vs
             Nothing -> fallback

        (_, Con c vs) -> do
           md <- isEtaRecordTypeHH aHH
           case md of
             Just (d, parsHH) -> do
               (tel, us) <- liftTCM $ etaExpandRecord d (leftHH parsHH) u
               b <- liftTCM $ getRecordConstructorType d
               bHH <- ureduce (b `applyHH` parsHH)
               unifyConstructorArgs bHH us vs
             Nothing -> fallback

        -- Andreas, 2011-05-30: If I put checkEquality below, then Issue81 fails
        -- because there are definitions blocked by flexibles that need postponement
        _  -> fallback


    unify :: Type -> Term -> Term -> Unify ()
    unify a = unifyHH (Hom a)

    -- The contexts are transient when unifying, so we should just instantiate to
    -- constructor heads and generate fresh metas for the arguments. Beware of
    -- constructors that aren't fully applied.
    instMetaE :: Type -> MetaId -> Elims -> Term -> TCM Bool
    instMetaE a m es v = do
      case allApplyElims es of
        Just us -> instMeta a m us v
        Nothing -> return False

    instMeta :: Type -> MetaId -> Args -> Term -> TCM Bool
    instMeta a m us v = do
      app <- inertApplication a v
      reportSDoc "tc.lhs.unify" 50 $
        sep [ text "inert"
              <+> sep [ text (show m), text (show us), parens $ prettyTCM v ]
            , nest 2 $ text "==" <+> text (show app)
            ]
      case app of
        Nothing -> return False
        Just (v', b, vs) -> do
            margs <- do
              -- The new metas should have the same dependencies as the original meta
              mv <- lookupMeta m

              -- Only generate metas for the arguments v' is actually applied to
              -- (in case of partial application)
              TelV tel0 _ <- telView b
              let tel = telFromList $ take (length vs) $ telToList tel0
                  b'  = telePi tel (sort Prop)
              withMetaInfo' mv $ do
                tel <- getContextTelescope
                -- important: create the meta in the same environment as the original meta
                newArgsMetaCtx b' tel us
            noConstraints $ assignV DirEq m us (v' `apply` margs)
            return True
          `catchError` \_ -> return False

    inertApplication :: Type -> Term -> TCM (Maybe (Term, Type, Args))
    inertApplication a v =
      case ignoreSharing v of
        Con c vs -> fmap (\ b -> (Con c [], b, vs)) <$> dataOrRecordType c a
        Def d es | Just vs <- allApplyElims es -> do
          def <- getConstInfo d
          let ans = Just (Def d [], defType def, vs)
          return $ case theDef def of
            Datatype{} -> ans
            Record{}   -> ans
            Axiom{}    -> ans
            _          -> Nothing
        _        -> return Nothing

-- | Given the type of a constructor application the corresponding
-- data or record type, applied to its parameters (extracted from the
-- given type), is returned.
--
-- Precondition: The type has to correspond to an application of the
-- given constructor.
dataOrRecordType
  :: ConHead -- ^ Constructor name.
  -> Type  -- ^ Type of constructor application (must end in data/record).
  -> TCM (Maybe Type) -- ^ Type of constructor, applied to pars.
dataOrRecordType c a = fmap (\ (d, b, pars, _) -> b `apply` pars) <$> dataOrRecordType' c a

dataOrRecordType' ::
     ConHead -- ^ Constructor name.
  -> Type  -- ^ Type of constructor application (must end in data/record).
  -> TCM (Maybe (QName, Type, Args, Args))
           -- ^ Name of data/record type,
           --   type of constructor to be applied,
           --   data/record parameters, and
           --   data indices
dataOrRecordType' c a = do
  -- The telescope ends with a datatype or a record.
  (d, args) <- do
    TelV _ (El _ def) <- telView a
    let Def d es = ignoreSharing def
        args = fromMaybe __IMPOSSIBLE__ $ allApplyElims es
    return (d, args)
  def <- theDef <$> getConstInfo d
  case def of
    Datatype{dataPars = n} -> do
      a' <- defType <$> getConInfo c
      let (pars, ixs) = genericSplitAt n args
      return $ Just (d, a', pars, ixs)
    Record{} -> do
      a' <- getRecordConstructorType d
      return $ Just (d, a', args, [])
    _ -> return Nothing

-- | Heterogeneous situation.
--   @a1@ and @a2@ need to end in same datatype/record.
dataOrRecordTypeHH ::
     ConHead      -- ^ Constructor name.
  -> TypeHH     -- ^ Type(s) of constructor application (must end in same data/record).
  -> TCM (Maybe TypeHH) -- ^ Type of constructor, instantiated possibly heterogeneously to parameters.
dataOrRecordTypeHH c (Hom a) = fmap Hom <$> dataOrRecordType c a
dataOrRecordTypeHH c (Het a1 a2) = do
  r1 <- dataOrRecordType' c a1
  r2 <- dataOrRecordType' c a2  -- b2 may have different parameters than b1!
  return $ case (r1, r2) of
    (Just (d1, b1, pars1, _), Just (d2, b2, pars2, _)) | d1 == d2 -> Just $
        -- Andreas, 2011-09-15 if no parameters, we can stay homogeneous
        if null pars1 && null pars2 then Hom b1
         -- if parameters, go heterogeneous
         -- TODO: make this smarter, because parameters could be equal!
         else Het (b1 `apply` pars1) (b2 `apply` pars2)
    _ -> Nothing

dataOrRecordTypeHH' ::
     ConHead
  -> TypeHH
  -> TCM (Maybe (QName, Type, HomHet (Args, Args)))
dataOrRecordTypeHH' c (Hom a) = do
  r <- dataOrRecordType' c a
  case r of
    Just (d, a', pars, ixs) -> return $ Just (d, a', Hom (pars, ixs))
    Nothing                 -> return $ Nothing
dataOrRecordTypeHH' c (Het a1 a2) = do
  r1 <- dataOrRecordType' c a1
  r2 <- dataOrRecordType' c a2
  case (r1, r2) of
    (Just (d1, b1, pars1, ixs1), Just (d2, b2, pars2, ixs2)) | d1 == d2 -> do
      -- Same constructors have same types, of course.
      unless (b1 == b2) __IMPOSSIBLE__
      return $ Just $
        if null pars1 && null pars2 && null ixs1 && null ixs2
          then (d1, b1, Hom ([], []))
          else (d1, b1, Het (pars1, ixs1) (pars2, ixs2))
    _ -> return Nothing


-- | Return record type identifier if argument is a record type.
isEtaRecordTypeHH :: MonadTCM tcm => TypeHH -> tcm (Maybe (QName, HomHet Args))
isEtaRecordTypeHH (Hom a) = fmap (\ (d, ps) -> (d, Hom ps)) <$> liftTCM (isEtaRecordType a)
isEtaRecordTypeHH (Het a1 a2) = do
  m1 <- liftTCM $ isEtaRecordType a1
  m2 <- liftTCM $ isEtaRecordType a2
  case (m1, m2) of
    (Just (d1, as1), Just (d2, as2)) | d1 == d2 -> return $ Just (d1, Het as1 as2)
    _ -> return Nothing


-- | Views an expression (pair) as type shape.  Fails if not same shape.
data ShapeView a
  = PiSh (Dom a) (I.Abs a)
  | FunSh (Dom a) a
  | DefSh QName   -- ^ data/record
  | VarSh Nat     -- ^ neutral type
  | LitSh Literal -- ^ built-in type
  | SortSh
  | MetaSh        -- ^ some meta
  | ElseSh        -- ^ not a type or not definitely same shape
  deriving (Typeable, Show, Functor)

deriving instance (Subst t a, Eq  a) => Eq  (ShapeView a)
deriving instance (Subst t a, Ord a) => Ord (ShapeView a)

-- | Return the type and its shape.  Expects input in (u)reduced form.
shapeView :: Type -> Unify (Type, ShapeView Type)
shapeView t = do
  return . (t,) $ case ignoreSharing $ unEl t of
    Pi a (NoAbs _ b) -> FunSh a b
    Pi a (Abs x b) -> PiSh a (Abs x b)
    Def d vs       -> DefSh d
    Var x vs       -> VarSh x
    Lit l          -> LitSh l
    Sort s         -> SortSh
    MetaV m vs     -> MetaSh
    _              -> ElseSh

-- | Return the reduced type(s) and the common shape.
shapeViewHH :: TypeHH -> Unify (TypeHH, ShapeView TypeHH)
shapeViewHH (Hom a) = do
  (a, sh) <- shapeView a
  return (Hom a, fmap Hom sh)
shapeViewHH (Het a1 a2) = do
  (a1, sh1) <- shapeView a1
  (a2, sh2) <- shapeView a2
  return . (Het a1 a2,) $ case (sh1, sh2) of

    (PiSh d1@(Dom i1 a1) b1, PiSh (Dom i2 a2) b2)
      | argInfoHiding i1 == argInfoHiding i2 ->
      PiSh (Dom (setRelevance (min (getRelevance i1) (getRelevance i2)) i1)
                (Het a1 a2))
           (Abs (absName b1) (Het (absBody b1) (absBody b2)))

    (FunSh d1@(Dom i1 a1) b1, FunSh (Dom i2 a2) b2)
      | argInfoHiding i1 == argInfoHiding i2 ->
      FunSh (Dom (setRelevance (min (getRelevance i1) (getRelevance i2)) i1)
                 (Het a1 a2))
            (Het b1 b2)

    (DefSh d1, DefSh d2) | d1 == d2 -> DefSh d1
    (VarSh x1, VarSh x2) | x1 == x2 -> VarSh x1
    (LitSh l1, LitSh l2) | l1 == l2 -> LitSh l1
    (SortSh, SortSh)                -> SortSh
    _ -> ElseSh  -- not types, or metas, or not same shape


-- | @telViewUpToHH n t@ takes off the first @n@ function types of @t@.
-- Takes off all if $n < 0$.
telViewUpToHH :: Int -> TypeHH -> Unify TelViewHH
telViewUpToHH 0 t = return $ TelV EmptyTel t
telViewUpToHH n t = do
  (t, sh) <- shapeViewHH =<< liftTCM (traverse reduce t)
  case sh of
    PiSh a b  -> absV a (absName b) <$> telViewUpToHH (n-1) (absBody b)
    FunSh a b -> absV a underscore <$> telViewUpToHH (n-1) (raise 1 b)
    _         -> return $ TelV EmptyTel t
  where
    absV a x (TelV tel t) = TelV (ExtendTel a (Abs x tel)) t

isSet :: Term -> TCM Bool
isSet a = do
  a <- reduce a
  case ignoreSharing a of
    Def d es -> do
      let args = fromMaybe __IMPOSSIBLE__ $ allApplyElims es
      Defn{ defType = dtype, theDef = def } <- getConstInfo d
      reportSDoc "tc.lhs.unify.isset" 50 $ text "Checking whether " <+> prettyTCM a <+> text " is a set..."
      case def of
        Datatype{ dataPars = npars, dataCons = cs, dataMutual = [], dataAbstr = ConcreteDef } -> do
           let pars       = take npars args
               TelV tel _ = telView' $ dtype `apply` pars
               ixtypes    = map (unEl . unDom) $ flattenTel tel
           ifNotM (allM ixtypes isSet) (return False) $ allM cs $ \c -> do
             ctype <- defType <$> getConstInfo c
             checkConstructorType d $ ctype `apply` pars
        Record{ recConType = ctype } -> checkConstructorType d $ ctype `apply` args
        _ -> return False
    _ -> return False
  where
    checkConstructorType :: QName -> Type -> TCM Bool
    checkConstructorType d a = do
      let TelV tel _ = telView' a
      allM (map (unEl . unDom) $ flattenTel tel) $ \b -> case ignoreSharing b of
        Def d' _ | d == d' -> return True
        _ -> isSet b
