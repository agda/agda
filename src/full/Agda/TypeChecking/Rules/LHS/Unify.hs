{-# LANGUAGE CPP, MultiParamTypeClasses, FlexibleInstances, TupleSections,
    GeneralizedNewtypeDeriving,
    DeriveDataTypeable, DeriveFunctor, DeriveFoldable, DeriveTraversable #-}

module Agda.TypeChecking.Rules.LHS.Unify where

import Control.Applicative hiding (empty)
import Control.Monad.State
import Control.Monad.Reader
import Control.Monad.Error
import Control.Monad.Writer

import Data.Map (Map)
import qualified Data.Map as Map
import Data.List hiding (sort)

import Data.Generics (Typeable, Data)
import Data.Foldable (Foldable)
import Data.Traversable (Traversable,traverse)

import Agda.Syntax.Common
import Agda.Syntax.Internal
import Agda.Syntax.Literal
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
import Agda.Utils.Size

newtype Unify a = U { unUnify :: ReaderT UnifyEnv (WriterT UnifyOutput (ExceptionT UnifyException (StateT UnifyState TCM))) a }
  deriving (Monad, MonadIO, Functor, Applicative, MonadException UnifyException, MonadWriter UnifyOutput)

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

-- | Output the result of unification (success or maybe).
type UnifyOutput = Unifiable

emptyUOutput :: UnifyOutput
emptyUOutput = mempty

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

{-
-- | Check whether unification proceeded without postponement.
listenResult :: Unify () -> Unify UnifyOutput
listenResult m = snd <$> listen m
-}

-- | Check whether unification proceeded without postponement.
ifClean :: Unify () -> Unify a -> Unify a -> Unify a
ifClean m t e = do
  ok <- snd <$> listen m
  case ok of
    Definitely -> t
    Possibly ->   e

{-
-- | Check whether unification proceeded without postponement.
ifClean :: Unify a -> (a -> Unify b) -> (a -> Unify b) -> Unify b
ifClean m t e = do
  (ok, a) <- listen m
  case ok of
    Definitely -> t a
    Possibly ->   e a
-}

data Equality = Equal TypeHH Term Term
type Sub = Map Nat Term

data UnifyException
  = ConstructorMismatch Type Term Term
  | StronglyRigidOccurrence Type Term Term
  | GenericUnifyException String
  | TypeMismatch TypeHH Term Term -- ^ not valid type or different-shape types
  | HeterogeneousButNoMismatch

instance Error UnifyException where
  noMsg  = strMsg ""
  strMsg = GenericUnifyException

data UnifyState = USt { uniSub	  :: Sub
		      , uniConstr :: [Equality]
		      }

emptyUState = USt Map.empty []

constructorMismatch :: Type -> Term -> Term -> Unify a
constructorMismatch a u v = throwException $ ConstructorMismatch a u v

constructorMismatchHH :: TypeHH -> Term -> Term -> Unify a
constructorMismatchHH aHH = constructorMismatch (leftHH aHH)
  -- do not report heterogenity
{-
constructorMismatchHH (Hom a) u v = constructorMismatch a u v
constructorMismatchHH (Het a1 a2) u v = constructorMismatch a1 u v
-}

typeMismatch :: TypeHH -> Term -> Term -> Unify a
typeMismatch aHH u v = throwException $ TypeMismatch aHH u v

{-
instance MonadReader TCEnv Unify where
  ask           = U . lift  $ ask
  local k (U m) = U . lift . lift . lift $ local k m
-}

instance MonadState TCState Unify where
  get = U . lift . lift . lift . lift $ get
  put = U . lift . lift . lift . lift . put

instance MonadTCM Unify where
  liftTCM = U . lift . lift . lift . lift

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
checkEqualities eqs = noConstraints $ mapM_ checkEq eqs
  where
    checkEq (Equal (Hom a) s t) = equalTerm a s t
    checkEq (Equal (Het{}) s t) = typeError $ GenericError $ "heterogeneous equality"

-- | Force equality now instead of postponing it using 'addEquality'.
checkEquality :: MonadTCM tcm => Type -> Term -> Term -> tcm ()
checkEquality a u v = noConstraints $ equalTerm a u v

-- | Try equality.  If constraints remain, postpone (enter unsafe mode).
--   Heterogeneous equalities cannot be tried nor reawakened,
--   so we can throw them away and flag "dirty".
checkEqualityHH :: TypeHH -> Term -> Term -> Unify ()
checkEqualityHH (Hom a) u v = do
    ok <- liftTCM $ noConstraints (True <$ equalTerm a u v)  -- no constraints left
            `catchError` \ err -> return False
    if ok then return () else addEquality a u v
checkEqualityHH aHH@(Het a1 a2) u v = -- reportPostponing -- enter "dirty" mode
    addEqualityHH aHH u v -- postpone, enter "dirty" mode
{-
checkEqualityHH (Het a1 a2) u v = noConstraints $ do
  equalType a1 a2
  equalTerm a1 u v
-}
{-
checkEqualityHH :: MonadTCM tcm => TypeHH -> Term -> Term -> tcm ()
checkEqualityHH aHH u v = do
  a  <- forceHom aHH
  cs <- equalTerm a u v
  if null cs then return () else addEquality a u v
-}


-- | Check whether heterogeneous situation is really homogeneous.
--   If not, give up.
forceHom :: MonadTCM tcm => TypeHH -> tcm Type
forceHom (Hom a) = return a
forceHom (Het a1 a2) = do
  noConstraints $ equalType a1 a2
  return a1

addEquality :: Type -> Term -> Term -> Unify ()
addEquality a = addEqualityHH (Hom a)

addEqualityHH :: TypeHH -> Term -> Term -> Unify ()
addEqualityHH aHH u v = do
  reportPostponing
  U $ modify $ \s -> s { uniConstr = Equal aHH u v : uniConstr s }

{-
addEquality :: Type -> Term -> Term -> Unify ()
addEquality a u v = do
  reportPostponing
  U $ modify $ \s -> s { uniConstr = Equal a u v : uniConstr s }
-}

{-
addEquality :: Type -> Term -> Term -> Unify ()
addEquality a u v = do
   p <- askPostpone
   case p of
     MayPostpone ->  do
       reportPostponing
       U $ modify $ \s -> s { uniConstr = Equal a u v : uniConstr s }
     MayNotPostpone -> checkEquality a u v
-}

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

    NoOccurrence  -> return ()  -- this includes irrelevant occurrences!

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

data UnificationResult = Unifies Substitution | NoUnify Type Term Term | DontKnow (Maybe TCErr)

-- | Are we in a homogeneous (one type) or heterogeneous (two types) situation?
data HomHet a
  = Hom a    -- ^ homogeneous
  | Het a a  -- ^ heterogeneous
  deriving (Typeable, Data, Show, Eq, Ord, Functor, Foldable, Traversable)

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

instance (Raise a) => Raise (HomHet a) where
  raiseFrom n m  = fmap (raiseFrom n m)
  renameFrom n f = fmap (renameFrom n f)

instance (Subst a) => Subst (HomHet a) where
  substUnder n u = fmap (substUnder n u)
  substs us      = fmap (substs us)

instance (PrettyTCM a) => PrettyTCM (HomHet a) where
  prettyTCM (Hom a) = prettyTCM a
  prettyTCM (Het a1 a2) = prettyTCM a1 <+> text "||" <+> prettyTCM a2

type TermHH    = HomHet Term
type TypeHH    = HomHet Type
--type FunViewHH = FunV TypeHH
type TelHH     = Tele (Arg TypeHH)
type TelViewHH = TelV TypeHH

absAppHH :: SubstHH t tHH => Abs t -> TermHH -> tHH
absAppHH (Abs _ t) u = substHH u t

substHH :: SubstHH t tHH => TermHH -> t -> tHH
substHH = substUnderHH 0

-- | @substHH u t@ substitutes @u@ for the 0th variable in @t@.
class SubstHH t tHH where
  substUnderHH :: Nat -> TermHH -> t -> tHH

instance (Free a, Subst a) => SubstHH (HomHet a) (HomHet a) where
  substUnderHH n (Hom u) t = fmap (substUnder n u) t
  substUnderHH n (Het u1 u2) (Hom t) =
    if n `relevantIn` t then Het (substUnder n u1 t) (substUnder n u2 t)
     else Hom (substUnder n u1 t)
  substUnderHH n (Het u1 u2) (Het t1 t2) = Het (substUnder n u1 t1) (substUnder n u2 t2)

instance SubstHH Term (HomHet Term) where
  substUnderHH n uHH t = fmap (\ u -> substUnder n u t) uHH

instance SubstHH Type (HomHet Type) where
  substUnderHH n uHH (El s t) = fmap (\ u -> El s $ substUnder n u t) uHH
-- fmap $ fmap (\ (El s v) -> El s $ substUnderHH n u v)
  -- we ignore sorts in substitution, since they do not contain
  -- terms we can match on

instance SubstHH a b => SubstHH (Arg a) (Arg b) where
  substUnderHH n u = fmap $ substUnderHH n u

instance SubstHH a b => SubstHH (Abs a) (Abs b) where
  substUnderHH n u = fmap $ substUnderHH (n+1) u

instance (SubstHH a a', SubstHH b b') => SubstHH (a,b) (a',b') where
    substUnderHH n u (x,y) = (substUnderHH n u x, substUnderHH n u y)

instance SubstHH a b => SubstHH (Tele a) (Tele b) where
  substUnderHH n u  EmptyTel         = EmptyTel
  substUnderHH n u (ExtendTel t tel) = uncurry ExtendTel $ substUnderHH n u (t, tel)

-- | Unify indices.
unifyIndices_ :: MonadTCM tcm => FlexibleVars -> Type -> [Arg Term] -> [Arg Term] -> tcm Substitution
unifyIndices_ flex a us vs = liftTCM $ do
  r <- unifyIndices flex a us vs
  case r of
    Unifies sub         -> return sub
    DontKnow Nothing    -> typeError $ GenericError $ "unification failed due to postponed problems"
    DontKnow (Just err) -> throwError err
    NoUnify a u v       -> typeError $ UnequalTerms CmpEq u v a

dontKnow :: UnificationResult
dontKnow = DontKnow Nothing
-- $ GenericError $ "unification failed due to postponed problems"

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
    (r, USt s eqs) <- flip runStateT emptyUState . runExceptionT . runWriterT . flip runReaderT emptyUEnv . unUnify $ do
        ifClean (unifyArgs a us vs)
          -- clean: continue unifying
          (recheckConstraints)
          -- dirty: just check equalities to trigger error message
          (recheckEqualities) -- (throwException HeterogeneousButNoMismatch)

    case r of
      Left (HeterogeneousButNoMismatch)     -> return $ dontKnow
      Left (TypeMismatch          aHH u v)  -> return $ dontKnow
      Left (ConstructorMismatch     a u v)  -> return $ NoUnify a u v
      -- Andreas 2011-04-14:
      Left (StronglyRigidOccurrence a u v)  -> return $ NoUnify a u v
      Left (GenericUnifyException     err)  -> fail err
      Right _                               -> do
        checkEqualities $ substs (makeSubstitution s) eqs
        let n = maximum $ (-1) : flex
        return $ Unifies $ flattenSubstitution [ Map.lookup i s | i <- [0..n] ]
  `catchError` \err -> return $ DontKnow $ Just err
  where
    flexible i = i `elem` flex

    flexibleTerm (Var i []) = flexible i
    flexibleTerm _          = False

    {- Andreas, 2011-09-12
       We unify constructors in heterogeneous situations, as long
       as the two types have the same shape (construct the same datatype).
     -}

    unifyConstructorArgs ::
         TypeHH  -- ^ The type of the constructor, instantiated to the parameters.
                 --   Possibly heterogeneous, since pars of lhs and rhs might differ.
      -> [Arg Term]  -- ^ the arguments of the constructor (lhs)
      -> [Arg Term]  -- ^ the arguments of the constructor (rhs)
      -> Unify ()
    unifyConstructorArgs a12 [] [] = return ()
    unifyConstructorArgs a12 vs1 vs2 = do
      reportSDoc "tc.lhs.unify" 15 $ sep
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
         TelHH  -- ^ The telescope(s) of the constructor args    [length = n].
      -> [Arg Term]  -- ^ the arguments of the constructor (lhs) [length = n].
      -> [Arg Term]  -- ^ the arguments of the constructor (rhs) [length = n].
      -> Unify ()
    unifyConArgs _ (_ : _) [] = __IMPOSSIBLE__
    unifyConArgs _ [] (_ : _) = __IMPOSSIBLE__
    unifyConArgs _ []      [] = return ()
    unifyConArgs EmptyTel _ _ = __IMPOSSIBLE__
    unifyConArgs tel0@(ExtendTel a@(Arg _ rel bHH) tel) us0@(arg@(Arg _ _ u) : us) vs0@(Arg _ _ v : vs) = do
      reportSDoc "tc.lhs.unify" 15 $ sep
        [ text "unifyConArgs"
	-- , nest 2 $ parens (prettyTCM tel0)
	, nest 2 $ prettyList $ map prettyTCM us0
	, nest 2 $ prettyList $ map prettyTCM vs0
	, nest 2 $ text "at telescope" <+> prettyTCM bHH <+> text "..."
        ]
      -- Andreas, Ulf, 2011-09-08 (AIM XVI)
      -- in case of dependent function type, we cannot postpone
      -- unification of u and v, otherwise us or vs might be ill-typed
      -- skip irrelevant parts
      uHH <- if (rel == Irrelevant) then return $ Hom u else
               ifClean (unifyHH bHH u v) (return $ Hom u) (return $ Het u v)
{-             do
               res <- listenResult $ unifyHH b u v
               case res of
                 Definitely -> return $ Hom u
                 Possibly -> return $ Het u v
-}
      uHH <- traverse ureduce uHH
      unifyConArgs (tel `absAppHH` uHH) us vs


{-
    unifyArgs :: Type -> [Arg Term] -> [Arg Term] -> Unify ()
    unifyArgs a = unifyArgsHH (Hom a)
-}

    -- | Used for arguments of a 'Def', not 'Con'.
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
      where dependent (Pi b c) = 0 `relevantIn` absBody c
            dependent _        = False

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

    -- | Possibly heterogeneous unification (but at same-shaped types).
    --   In het. situations, we only search for a mismatch!
    --
    -- TODO: eta for records!
    unifyHH :: TypeHH -> Term -> Term -> Unify ()
    unifyHH aHH u v = do
      u <- constructorForm =<< ureduce u
      v <- constructorForm =<< ureduce v
      reportSDoc "tc.lhs.unify" 15 $
	sep [ text "unifyHH"
	    , nest 2 $ parens $ prettyTCM u
	    , nest 2 $ parens $ prettyTCM v
	    , nest 2 $ text ":" <+> prettyTCM aHH
	    ]
      -- obtain the (== Size) function
      isSizeName <- isSizeNameTest

      -- check whether types have the same shape
      (aHH, sh) <- shapeViewHH aHH
      case sh of
        ElseSh  -> typeMismatch aHH u v  -- not a type or not same types

        DefSh d -> if isSizeName d then unifySizes u v
                                   else unifyAtomHH aHH u v
        _ -> unifyAtomHH aHH u v

    unifyAtomHH :: TypeHH -> Term -> Term -> Unify ()
    unifyAtomHH aHH u v = do
      let homogeneous = isHom aHH
          a = fromHom aHH  -- ^ use only if 'homogeneous' holds!
      reportSDoc "tc.lhs.unify" 15 $
	sep [ text "unifyAtom"
	    , nest 2 $ prettyTCM u <> if flexibleTerm u then text " (flexible)" else empty
            , nest 2 $ text "=?="
	    , nest 2 $ prettyTCM v <> if flexibleTerm v then text " (flexible)" else empty
	    , nest 2 $ text ":" <+> prettyTCM aHH
	    ]
      case (u, v) of
        -- Ulf, 2011-06-19
        -- We don't want to worry about levels here.
        (Level l, v) -> do
            u <- liftTCM $ reallyUnLevelView l
            unifyAtomHH aHH u v
        (u, Level l) -> do
            v <- liftTCM $ reallyUnLevelView l
            unifyAtomHH aHH u v
	(Var i us, Var j vs) | i == j  -> checkEqualityHH aHH u v
	(Var i [], v) | homogeneous && flexible i -> i |->> (v, a)
	(u, Var j []) | homogeneous && flexible j -> j |->> (u, a)
	(Con c us, Con c' vs)
          | c == c' -> do
              r <- dataOrRecordTypeHH c aHH
              case r of
                Just a'HH -> unifyConstructorArgs a'HH us vs
                Nothing   -> typeMismatch aHH u v
          | otherwise -> constructorMismatchHH aHH u v
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
                else checkEqualityHH aHH u v
          -- Andreas, 2011-05-30: if heads disagree, abort
          -- but do not raise "mismatch" because otherwise type constructors
          -- would be distinct
          | otherwise -> typeError $ UnequalTerms CmpEq u v a
        (Lit l1, Lit l2)
          | l1 == l2  -> return ()
          | otherwise -> constructorMismatchHH aHH u v

        -- We can instantiate metas if the other term is inert (constructor application)
        -- Andreas, 2011-09-13: test/succeed/IndexInference needs this feature.
        (MetaV m us, v) | homogeneous -> do
            ok <- liftTCM $ instMeta a m us v
            reportSDoc "tc.lhs.unify" 40 $
              vcat [ fsep [ text "inst meta", text $ if ok then "(ok)" else "(not ok)" ]
                   , nest 2 $ sep [ prettyTCM u, text ":=", prettyTCM =<< normalise u ]
                   ]
            if ok then unify a u v
                  else addEquality a u v
        (u, MetaV m vs) | homogeneous -> do
            ok <- liftTCM $ instMeta a m vs u
            reportSDoc "tc.lhs.unify" 40 $
              vcat [ fsep [ text "inst meta", text $ if ok then "(ok)" else "(not ok)" ]
                   , nest 2 $ sep [ prettyTCM v, text ":=", prettyTCM =<< normalise v ]
                   ]
            if ok then unify a u v
                  else addEquality a u v
        -- Andreas, 2011-05-30: If I put checkEquality below, then Issue81 fails
        -- because there are definitions blocked by flexibles that need postponement
	_  -> checkEqualityHH aHH u v

    unify :: Type -> Term -> Term -> Unify ()
    unify a = unifyHH (Hom a)
{-
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
-}

    unifyAtom :: Type -> Term -> Term -> Unify ()
    unifyAtom a = unifyAtomHH (Hom a)

{-
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
-}
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
        Con c vs -> fmap (\ b -> (Con c [], b, vs)) <$> dataOrRecordType c a
{-
        Con c vs -> do
          b <- dataOrRecordType c a
          return $ Just (Con c [], b, vs)
-}
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

{-
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
-}
dataOrRecordType :: MonadTCM tcm
  => QName -- ^ Constructor name.
  -> Type  -- ^ Type of constructor application (must end in data/record).
  -> tcm (Maybe Type) -- ^ Type of constructor, applied to pars.
dataOrRecordType c a = fmap snd <$> dataOrRecordType' c a

dataOrRecordType' :: MonadTCM tcm
  => QName -- ^ Constructor name.
  -> Type  -- ^ Type of constructor application (must end in data/record).
  -> tcm (Maybe (QName, -- ^ Name of data/record type.
                 Type))  -- ^ Type of constructor, applied to pars.
dataOrRecordType' c a = do
  -- The telescope ends with a datatype or a record.
  TelV _ (El _ (Def d args)) <- telView a
  def <- theDef <$> getConstInfo d
  r <- case def of
    Datatype{dataPars = n} -> Just . ((,) n) . defType <$> getConstInfo c
    Record  {recPars  = n} -> Just . ((,) n) <$> getRecordConstructorType d
    _		           -> return Nothing
  return $ fmap (\ (n, a') -> (d, a' `apply` genericTake n args)) r

-- | Heterogeneous situation.
--   @a1@ and @a2@ need to end in same datatype/record.
dataOrRecordTypeHH :: MonadTCM tcm
  => QName      -- ^ Constructor name.
  -> TypeHH     -- ^ Type(s) of constructor application (must end in same data/record).
  -> tcm (Maybe TypeHH) -- ^ Type of constructor, instantiated possibly heterogeneously to parameters.
dataOrRecordTypeHH c (Hom a) = fmap Hom <$> dataOrRecordType c a
dataOrRecordTypeHH c (Het a1 a2) = do
  r1 <- dataOrRecordType' c a1
  r2 <- dataOrRecordType' c a2  -- b2 may have different parameters than b1!
  return $ case (r1, r2) of
    (Just (d1, b1), Just (d2, b2)) | d1 == d2 -> Just $ Het b1 b2
    _ -> Nothing

{-
dataOrRecordType' :: MonadTCM tcm
  => QName -- ^ Constructor name.
  -> Type  -- ^ Type of constructor application (must end in data/record).
  -> tcm (QName, -- ^ Name of data/record type.
          Type)  -- ^ Type of constructor, applied to pars.
dataOrRecordType' c a = do
  -- The telescope ends with a datatype or a record.
  TelV _ (El _ (Def d args)) <- telView a
  def <- theDef <$> getConstInfo d
  (n, a')  <- case def of
    Datatype{dataPars = n} -> ((,) n) . defType <$> getConstInfo c
    Record  {recPars  = n} -> ((,) n) <$> getRecordConstructorType d
    _		           -> __IMPOSSIBLE__
  return (d, a' `apply` genericTake n args)
-}

{-
-- | Heterogeneous situation.
--   @a1@ and @a2@ need to end in same datatype/record.
dataOrRecordTypeHH :: MonadTCM tcm
  => QName      -- ^ Constructor name.
  -> TypeHH     -- ^ Type(s) of constructor application (must end in same data/record).
  -> tcm TypeHH -- ^ Type of constructor, instantiated possibly heterogeneously to parameters.
dataOrRecordTypeHH c (Hom a) = Hom <$> dataOrRecordType c a
dataOrRecordTypeHH c (Het a1 a2) = do
  (d1, b1) <- dataOrRecordType' c a1
  (d2, b2) <- dataOrRecordType' c a2  -- b2 may have different parameters than b1!
  when (d1 /= d2) $ __IMPOSSIBLE__    -- a1 and a2 have same shape!
  return $ Het b1 b2
-}

-- | Views an expression (pair) as type shape.  Fails if not same shape.
data ShapeView a
  = PiSh (Arg a) (Abs a)
  | FunSh (Arg a) a
  | DefSh QName   -- ^ data/record
  | VarSh Nat     -- ^ neutral type
  | LitSh Literal -- ^ built-in type
  | SortSh
  | MetaSh        -- ^ some meta
  | ElseSh        -- ^ not a type or not definitely same shape
  deriving (Typeable, Data, Show, Eq, Ord, Functor)

-- | Return the reduced type and its shape.
shapeView :: MonadTCM tcm => Type -> tcm (Type, ShapeView Type)
shapeView t = do
  t <- reduce t  -- also instantiates meta in head position
  return . (t,) $ case unEl t of
    Pi a (Abs x b) -> PiSh a (Abs x b)
    Fun a b        -> FunSh a b
    Def d vs       -> DefSh d
    Var x vs       -> VarSh x
    Lit l          -> LitSh l
    Sort s         -> SortSh
    MetaV m vs     -> MetaSh
    _              -> ElseSh

-- | Return the reduced type(s) and the common shape.
shapeViewHH :: MonadTCM tcm => TypeHH -> tcm (TypeHH, ShapeView TypeHH)
shapeViewHH (Hom a) = do
  (a, sh) <- shapeView a
  return (Hom a, fmap Hom sh)
shapeViewHH (Het a1 a2) = do
  (a1, sh1) <- shapeView a1
  (a2, sh2) <- shapeView a2
  return . (Het a1 a2,) $ case (sh1, sh2) of

    (PiSh (Arg h1 r1 a1) (Abs x1 b1), PiSh (Arg h2 r2 a2) (Abs x2 b2))
      | h1 == h2 && x1 == x2 ->
      PiSh (Arg h1 (min r1 r2) (Het a1 a2)) (Abs x1 (Het b1 b2))

    (FunSh (Arg h1 r1 a1) b1, FunSh (Arg h2 r2 a2) b2)
      | h1 == h2 ->
      FunSh (Arg h1 (min r1 r2) (Het a1 a2)) (Het b1 b2)

    (DefSh d1, DefSh d2) | d1 == d2 -> DefSh d1
    (VarSh x1, VarSh x2) | x1 == x2 -> VarSh x1
    (LitSh l1, LitSh l2) | l1 == l2 -> LitSh l1
    (SortSh, SortSh)                -> SortSh
    _ -> ElseSh  -- not types, or metas, or not same shape


-- | @telViewUpToHH n t@ takes off the first @n@ function types of @t@.
-- Takes off all if $n < 0$.
telViewUpToHH :: MonadTCM tcm => Int -> TypeHH -> tcm TelViewHH
telViewUpToHH 0 t = return $ TelV EmptyTel t
telViewUpToHH n t = do
  (t, sh) <- shapeViewHH t
  case sh of
    PiSh a (Abs x b) -> absV a x   <$> telViewUpToHH (n-1) b
    FunSh a b	     -> absV a "_" <$> telViewUpToHH (n-1) (raise 1 b)
    _		     -> return $ TelV EmptyTel t
  where
    absV a x (TelV tel t) = TelV (ExtendTel a (Abs x tel)) t
