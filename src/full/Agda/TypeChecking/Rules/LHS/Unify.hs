{-# LANGUAGE CPP, MultiParamTypeClasses, GeneralizedNewtypeDeriving #-}

module Agda.TypeChecking.Rules.LHS.Unify where

import Control.Applicative hiding (empty)
import Control.Monad.State
import Control.Monad.Reader
import Control.Monad.Error

import Data.Map (Map)
import qualified Data.Map as Map
import Data.List hiding (sort)
import Data.Traversable (traverse)

import Agda.Syntax.Common
import Agda.Syntax.Internal
import Agda.Syntax.Position

import Agda.TypeChecking.Monad
import Agda.TypeChecking.Monad.Exception
import Agda.TypeChecking.Conversion -- equalTerm
import Agda.TypeChecking.Constraints
import Agda.TypeChecking.Level (reallyUnLevelView)
import Agda.TypeChecking.Reduce
import Agda.TypeChecking.Pretty
import Agda.TypeChecking.Substitute hiding (Substitution)
import Agda.TypeChecking.Telescope
import Agda.TypeChecking.Free
import Agda.TypeChecking.Records
import Agda.TypeChecking.Primitive (constructorForm)
import Agda.TypeChecking.MetaVars (assignV, newArgsMetaCtx)
import Agda.TypeChecking.EtaContract
import Agda.Interaction.Options (optInjectiveTypeConstructors)

import Agda.TypeChecking.Rules.LHS.Problem

#include "../../../undefined.h"
import Agda.Utils.Impossible

newtype Unify a = U { unUnify :: ReaderT UnifyEnv (ExceptionT UnifyException (StateT UnifyState TCM)) a }
  deriving (Monad, MonadIO, Functor, Applicative, MonadException UnifyException)

instance MonadReader TCEnv Unify where
  ask = U $ ReaderT $ \ _ -> ask
  local cont (U (ReaderT f)) = U $ ReaderT $ \ a -> local cont (f a)

data UnifyMayPostpone = MayPostpone | MayNotPostpone

type UnifyEnv = UnifyMayPostpone
emptyUEnv   = MayPostpone

noPostponing :: Unify a -> Unify a
noPostponing (U (ReaderT f)) = U . ReaderT . const $ f MayNotPostpone

askPostpone :: Unify UnifyMayPostpone
askPostpone = U . ReaderT $ return

data Equality = Equal Type Term Term
type Sub = Map Nat Term

data UnifyException = ConstructorMismatch Type Term Term
                    | StronglyRigidOccurrence Type Term Term
                    | GenericUnifyException String

instance Error UnifyException where
  noMsg  = strMsg ""
  strMsg = GenericUnifyException

data UnifyState = USt { uniSub	  :: Sub
		      , uniConstr :: [Equality]
		      }

emptyUState = USt Map.empty []

constructorMismatch :: Type -> Term -> Term -> Unify a
constructorMismatch a u v = throwException $ ConstructorMismatch a u v

{-
instance MonadReader TCEnv Unify where
  ask           = U . lift  $ ask
  local k (U m) = U . lift . lift . lift $ local k m
-}

instance MonadState TCState Unify where
  get = U . lift . lift . lift $ get
  put = U . lift . lift . lift . put

instance MonadTCM Unify where
  liftTCM = U . lift . lift . lift

instance Subst Equality where
  substs us	 (Equal a s t) = Equal (substs us a)	  (substs us s)	     (substs us t)
  substUnder n u (Equal a s t) = Equal (substUnder n u a) (substUnder n u s) (substUnder n u t)

getSub :: Unify Sub
getSub = U $ gets uniSub

onSub :: (Sub -> a) -> Unify a
onSub f = U $ gets $ f . uniSub

modSub :: (Sub -> Sub) -> Unify ()
modSub f = U $ modify $ \s -> s { uniSub = f $ uniSub s }

checkEqualities :: [Equality] -> TCM ()
checkEqualities eqs = noConstraints $ concat <$> mapM checkEq eqs
  where
    checkEq (Equal a s t) = equalTerm a s t

-- | Force equality now instead of postponing it using 'addEquality'.
checkEquality :: MonadTCM tcm => Type -> Term -> Term -> tcm ()
checkEquality a u v = noConstraints $ equalTerm a u v

addEquality :: Type -> Term -> Term -> Unify ()
addEquality a u v = do
   p <- askPostpone
   case p of
     MayPostpone ->  U $ modify $ \s -> s { uniConstr = Equal a u v : uniConstr s }
     MayNotPostpone -> checkEquality a u v

takeEqualities :: Unify [Equality]
takeEqualities = U $ do
  s <- get
  put $ s { uniConstr = [] }
  return $ uniConstr s

-- | Includes flexible occurrences, metas need to be solved. TODO: relax?
--   TODO: later solutions may remove flexible occurences
occursCheck :: Nat -> Term -> Type -> Unify ()
occursCheck i u a = do
  let fv = freeVars u
      v  = Var i []
  case occurrence i fv of
    -- Andreas, 2011-04-14
    -- a strongly rigid recursive occurrences signals unsolvability
    StronglyRigid -> do
      reportSDoc "tc.lhs.unify" 20 $ prettyTCM v <+> text "occurs strongly rigidly in" <+> prettyTCM u
      throwException $ StronglyRigidOccurrence a v u

    NoOccurrence  -> return ()

    -- any other recursive occurrence leads to unclear situation
    _             -> do
      reportSDoc "tc.lhs.unify" 20 $ prettyTCM v <+> text "occurs in" <+> prettyTCM u
      typeError $ UnequalTerms CmpEq v u a

-- | Assignment with preceding occurs check.
(|->) :: Nat -> (Term, Type) -> Unify ()
i |-> (u, a) = do
  occursCheck i u a
  reportSDoc "tc.lhs.unify" 15 $ prettyTCM (Var i []) <+> text ":=" <+> prettyTCM u
  modSub $ Map.insert i (killRange u)

makeSubstitution :: Sub -> [Term]
makeSubstitution sub = map val [0..]
  where
    val i = maybe (Var i []) id $ Map.lookup i sub

-- | Apply the current substitution on a term and reduce to weak head normal form.
ureduce :: Term -> Unify Term
ureduce u = doEtaContractImplicit $ do
  rho <- onSub makeSubstitution
  liftTCM $ etaContract =<< normalise (substs rho u)
-- Andreas, 2011-06-22, fix related to issue 423
-- To make eta contraction work better, I switched reduce to normalise.
-- I hope the performance penalty is not big (since we are dealing with
-- l.h.s. terms only).
-- A systematic solution would make unification type-directed and
-- eta-insensitive...
--   liftTCM $ etaContract =<< reduce (substs rho u)

-- | Take a substitution σ and ensure that no variables from the domain appear
--   in the targets. The context of the targets is not changed.
--   TODO: can this be expressed using makeSubstitution and substs?
flattenSubstitution :: Substitution -> Substitution
flattenSubstitution s = foldr instantiate s is
  where
    -- instantiated variables
    is = [ i | (i, Just _) <- zip [0..] s ]

    instantiate :: Nat -> Substitution -> Substitution
    instantiate i s = map (fmap $ inst i u) s
      where
	Just u = s !! fromIntegral i

    inst :: Nat -> Term -> Term -> Term
    inst i u v = substs us v
      where us = [var j | j <- [0..i - 1] ] ++ [u] ++ [var j | j <- [i + 1..] ]
	    var j = Var j []

data UnificationResult = Unifies Substitution | NoUnify Type Term Term | DontKnow TCErr

-- | Unify indices.
unifyIndices_ :: MonadTCM tcm => FlexibleVars -> Type -> [Arg Term] -> [Arg Term] -> tcm Substitution
unifyIndices_ flex a us vs = liftTCM $ do
  r <- unifyIndices flex a us vs
  case r of
    Unifies sub   -> return sub
    DontKnow err  -> throwError err
    NoUnify a u v -> typeError $ UnequalTerms CmpEq u v a

unifyIndices :: MonadTCM tcm => FlexibleVars -> Type -> [Arg Term] -> [Arg Term] -> tcm UnificationResult
unifyIndices flex a us vs = liftTCM $ do
    reportSDoc "tc.lhs.unify" 10 $
      sep [ text "unifyIndices"
          , nest 2 $ text (show flex)
          , nest 2 $ parens (prettyTCM a)
          , nest 2 $ prettyList $ map prettyTCM us
          , nest 2 $ prettyList $ map prettyTCM vs
          , nest 2 $ text "context: " <+> (prettyTCM =<< getContextTelescope)
          ]
    (r, USt s eqs) <- flip runStateT emptyUState . runExceptionT . flip runReaderT emptyUEnv . unUnify $
                      unifyArgs a us vs >> recheckConstraints

    case r of
      Left (ConstructorMismatch     a u v)  -> return $ NoUnify a u v
      -- Andreas 2011-04-14:
      Left (StronglyRigidOccurrence a u v)  -> return $ NoUnify a u v
      Left (GenericUnifyException     err)  -> fail err
      Right _                               -> do
        checkEqualities $ substs (makeSubstitution s) eqs
        let n = maximum $ (-1) : flex
        return $ Unifies $ flattenSubstitution [ Map.lookup i s | i <- [0..n] ]
  `catchError` \err -> return $ DontKnow err
  where
    flexible i = i `elem` flex

    flexibleTerm (Var i []) = flexible i
    flexibleTerm _          = False

    unifyArgs :: Type -> [Arg Term] -> [Arg Term] -> Unify ()
    unifyArgs _ (_ : _) [] = __IMPOSSIBLE__
    unifyArgs _ [] (_ : _) = __IMPOSSIBLE__
    unifyArgs _ [] [] = return ()
    unifyArgs a us0@(arg@(Arg _ _ u) : us) vs0@(Arg _ _ v : vs) = do
      reportSDoc "tc.lhs.unify" 15 $ sep
        [ text "unifyArgs"
	, nest 2 $ parens (prettyTCM a)
	, nest 2 $ prettyList $ map prettyTCM us0
	, nest 2 $ prettyList $ map prettyTCM vs0
        ]
      a <- reduce a
      case funView $ unEl a of
	FunV b _  -> do
          -- Andreas, Ulf, 2011-09-08 (AIM XVI)
          -- in case of dependent function type, we cannot postpone
          -- unification of u and v, otherwise us or vs might be ill-typed
          let dep = dependent $ unEl a
          -- skip irrelevant parts
	  unless (argRelevance b == Irrelevant) $
            (if dep then noPostponing else id) $
              unify (unArg b) u v
          arg <- traverse ureduce arg
	  unifyArgs (a `piApply` [arg]) us vs
	_	  -> __IMPOSSIBLE__
      where dependent (Pi a b) = 0 `freeIn` absBody b
            dependent _        = False

    recheckConstraints :: Unify ()
    recheckConstraints = mapM_ unifyEquality =<< takeEqualities

    unifyEquality :: Equality -> Unify ()
    unifyEquality (Equal a u v) = unify a u v

    i |->> x = do
      i |-> x
      recheckConstraints

    unifySizes :: Term -> Term -> Unify ()
    unifySizes u v = do
      sz <- sizeType
      su <- sizeView u
      sv <- sizeView v
      case (su, sv) of
        (SizeSuc u, SizeSuc v) -> unify sz u v
        (SizeSuc u, SizeInf) -> unify sz u v
        (SizeInf, SizeSuc v) -> unify sz u v
        _                    -> unifyAtom sz u v

    -- TODO: eta for records here
    unify :: Type -> Term -> Term -> Unify ()
    unify a u v = do
      u <- constructorForm =<< ureduce u
      v <- constructorForm =<< ureduce v
      reportSDoc "tc.lhs.unify" 15 $
	sep [ text "unify"
	    , nest 2 $ parens $ prettyTCM u
	    , nest 2 $ parens $ prettyTCM v
	    , nest 2 $ text ":" <+> prettyTCM a
	    ]
      isSize <- isSizeType a
      if isSize then unifySizes u v
                else unifyAtom a u v

    unifyAtom :: Type -> Term -> Term -> Unify ()
    unifyAtom a u v = do
      reportSDoc "tc.lhs.unify" 15 $
	sep [ text "unifyAtom"
	    , nest 2 $ prettyTCM u <> if flexibleTerm u then text " (flexible)" else empty
            , nest 2 $ text "=?="
	    , nest 2 $ prettyTCM v <> if flexibleTerm v then text " (flexible)" else empty
	    , nest 2 $ text ":" <+> prettyTCM a
	    ]
      case (u, v) of
        -- Ulf, 2011-06-19
        -- We don't want to worry about levels here.
        (Level l, v) -> do
            u <- liftTCM $ reallyUnLevelView l
            unifyAtom a u v
        (u, Level l) -> do
            v <- liftTCM $ reallyUnLevelView l
            unifyAtom a u v
        -- Andreas, 2011-05-30
        -- Force equality now rather than postponing it with addEquality
	(Var i us, Var j vs) | i == j  -> checkEquality a u v
	(Var i [], v) | flexible i -> i |->> (v, a)
	(u, Var j []) | flexible j -> j |->> (u, a)
	(Con c us, Con c' vs)
          | c == c' -> do
              a' <- dataOrRecordType c a
              unifyArgs a' us vs
          | otherwise -> constructorMismatch a u v
        -- Definitions are ok as long as they can't reduce (i.e. datatypes/axioms)
	(Def d us, Def d' vs)
          | d == d' -> do
              -- d must be a data, record or axiom
              def <- getConstInfo d
              let ok = case theDef def of
                    Datatype{} -> True
                    Record{}   -> True
                    Axiom{}    -> True
                    _          -> False
              inj <- optInjectiveTypeConstructors <$> pragmaOptions
              if inj && ok
                then unifyArgs (defType def) us vs
                else addEquality a u v
{- Andreas: checkEquality breaks Data.Vec.Equality
   we need an injectivity test for data types, Vec A n is injective!
                else checkEquality a u v
                -- Andreas: force equality now instead of postponing
                -- We do not want to end up in a heterogeneous situation,
                -- where u and v have different types
-}
          -- Andreas, 2011-05-30: if heads disagree, abort
          -- but do not raise "mismatch" because otherwise type constructors
          -- would be distinct
          | otherwise -> typeError $ UnequalTerms CmpEq u v a
        (Lit l1, Lit l2)
          | l1 == l2  -> return ()
          | otherwise -> constructorMismatch a u v

        -- We can instantiate metas if the other term is inert (constructor application)
        (MetaV m us, v) -> do
            ok <- liftTCM $ instMeta a m us v
            reportSDoc "tc.lhs.unify" 40 $
              vcat [ fsep [ text "inst meta", text $ if ok then "(ok)" else "(not ok)" ]
                   , nest 2 $ sep [ prettyTCM u, text ":=", prettyTCM =<< normalise u ]
                   ]
            if ok then unify a u v
                  else addEquality a u v
        (u, MetaV m vs) -> do
            ok <- liftTCM $ instMeta a m vs u
            reportSDoc "tc.lhs.unify" 40 $
              vcat [ fsep [ text "inst meta", text $ if ok then "(ok)" else "(not ok)" ]
                   , nest 2 $ sep [ prettyTCM v, text ":=", prettyTCM =<< normalise v ]
                   ]
            if ok then unify a u v
                  else addEquality a u v
        -- Andreas, 2011-05-30: If I put checkEquality below, then Issue81 fails
        -- because there are definitions blocked by flexibles that need postponement
	_  -> addEquality a u v

    -- The contexts are transient when unifying, so we should just instantiate to
    -- constructor heads and generate fresh metas for the arguments. Beware of
    -- constructors that aren't fully applied.
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
              mi <- getMetaInfo <$> lookupMeta m

              -- Only generate metas for the arguments v' is actually applied to
              -- (in case of partial application)
              TelV tel0 _ <- telView b
              let tel = telFromList $ take (length vs) $ telToList tel0
                  b'  = telePi tel (sort Prop)
              withMetaInfo mi $ do
                tel <- getContextTelescope
                -- important: create the meta in the same environment as the original meta
                newArgsMetaCtx b' tel us
            noConstraints $ assignV m us (v' `apply` margs)
            return True
          `catchError` \_ -> return False

    inertApplication :: Type -> Term -> TCM (Maybe (Term, Type, Args))
    inertApplication a v =
      case v of
        Con c vs -> do
          b <- dataOrRecordType c a
          return $ Just (Con c [], b, vs)
        Def d vs -> do
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

dataOrRecordType :: MonadTCM tcm
                 => QName -- ^ Constructor name.
                 -> Type -> tcm Type
dataOrRecordType c a = do
  -- The telescope ends with a datatype or a record.
  TelV _ (El _ (Def d args)) <- telView a
  def <- theDef <$> getConstInfo d
  (n, a')  <- case def of
    Datatype{dataPars = n} -> ((,) n) . defType <$> getConstInfo c
    Record  {recPars  = n} -> ((,) n) <$> getRecordConstructorType d
    _		           -> __IMPOSSIBLE__
  return (a' `apply` genericTake n args)
