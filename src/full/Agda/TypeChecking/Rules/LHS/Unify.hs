{-# LANGUAGE CPP, MultiParamTypeClasses, FlexibleInstances, TupleSections,
    GeneralizedNewtypeDeriving,
    DeriveDataTypeable, DeriveFunctor, DeriveFoldable, DeriveTraversable #-}

module Agda.TypeChecking.Rules.LHS.Unify where

import Control.Arrow ((***), (&&&))
import Control.Applicative hiding (empty)
import Control.Monad.State
import Control.Monad.Reader
import Control.Monad.Error
import Control.Monad.Writer (WriterT(..), MonadWriter(..), Monoid(..))

import Data.Map (Map)
import qualified Data.Map as Map
import Data.List hiding (sort)

import Data.Typeable (Typeable)
import Data.Foldable (Foldable)
import Data.Traversable (Traversable,traverse)

import Agda.Syntax.Common
import Agda.Syntax.Internal as I
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
import qualified Agda.TypeChecking.Substitute as S
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

-- | Check whether unification proceeded without postponement.
ifClean :: Unify () -> Unify a -> Unify a -> Unify a
ifClean m t e = do
  ok <- snd <$> listen m
  case ok of
    Definitely -> t
    Possibly ->   e

data Equality = Equal TypeHH Term Term
type Sub = Map Nat Term

data UnifyException
  = ConstructorMismatch Type Term Term
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

constructorMismatchHH :: TypeHH -> Term -> Term -> Unify a
constructorMismatchHH aHH = constructorMismatch (leftHH aHH)
  -- do not report heterogenity

instance MonadState TCState Unify where
  get = U . lift . lift . lift . lift $ get
  put = U . lift . lift . lift . lift . put

instance MonadTCM Unify where
  liftTCM = U . lift . lift . lift . lift

instance Subst Equality where
  applySubst rho (Equal a s t) =
    Equal (applySubst rho a) (applySubst rho s) (applySubst rho t)

onSub :: (Sub -> a) -> Unify a
onSub f = U $ gets $ f . uniSub

modSub :: (Sub -> Sub) -> Unify ()
modSub f = U $ modify $ \s -> s { uniSub = f $ uniSub s }

checkEqualities :: [Equality] -> TCM ()
checkEqualities eqs = noConstraints $ mapM_ checkEq eqs
  where
    checkEq (Equal (Hom a) s t) = equalTerm a s t
    checkEq (Equal (Het a1 a2) s t) = typeError $ HeterogeneousEquality s a1 t a2

-- | Force equality now instead of postponing it using 'addEquality'.
checkEquality :: Type -> Term -> Term -> TCM ()
checkEquality a u v = noConstraints $ equalTerm a u v

-- | Try equality.  If constraints remain, postpone (enter unsafe mode).
--   Heterogeneous equalities cannot be tried nor reawakened,
--   so we can throw them away and flag "dirty".
checkEqualityHH :: TypeHH -> Term -> Term -> Unify ()
checkEqualityHH (Hom a) u v = do
    ok <- liftTCM $ noConstraints (True <$ equalTerm a u v)  -- no constraints left
            `catchError` \ err -> return False
    unless ok $ addEquality a u v
checkEqualityHH aHH@(Het a1 a2) u v = -- reportPostponing -- enter "dirty" mode
    addEqualityHH aHH u v -- postpone, enter "dirty" mode

-- | Check whether heterogeneous situation is really homogeneous.
--   If not, give up.
forceHom :: TypeHH -> TCM Type
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
      v  = var i
  case occurrence i fv of
    -- Andreas, 2011-04-14
    -- a strongly rigid recursive occurrences signals unsolvability
    StronglyRigid -> do
      liftTCM $ reportSDoc "tc.lhs.unify" 20 $ prettyTCM v <+> text "occurs strongly rigidly in" <+> prettyTCM u
      throwException $ StronglyRigidOccurrence a v u

    NoOccurrence  -> return ()  -- this includes irrelevant occurrences!

    -- any other recursive occurrence leads to unclear situation
    _             -> do
      liftTCM $ reportSDoc "tc.lhs.unify" 20 $ prettyTCM v <+> text "occurs in" <+> prettyTCM u
      typeError $ UnequalTerms CmpEq v u a

-- | Assignment with preceding occurs check.
(|->) :: Nat -> (Term, Type) -> Unify ()
i |-> (u, a) = do
  occursCheck i u a
  liftTCM $ reportSDoc "tc.lhs.unify" 15 $ prettyTCM (var i) <+> text ":=" <+> prettyTCM u
  modSub $ Map.insert i (killRange u)
  -- Apply substitution to itself (issue 552)
  rho  <- onSub id
  rho' <- traverse ureduce rho
  modSub $ const rho'

makeSubstitution :: Sub -> S.Substitution
makeSubstitution sub
  | Map.null sub = idS
  | otherwise    = map val [0 .. highestIndex] ++# raiseS (highestIndex + 1)
  where
    highestIndex = fst $ Map.findMax sub
    val i = maybe (var i) id $ Map.lookup i sub

-- | Apply the current substitution on a term and reduce to weak head normal form.
class UReduce t where
  ureduce :: t -> Unify t

instance UReduce Term where
  ureduce u = doEtaContractImplicit $ do
    rho <- onSub makeSubstitution
    liftTCM $ etaContract =<< normalise (applySubst rho u)
-- Andreas, 2011-06-22, fix related to issue 423
-- To make eta contraction work better, I switched reduce to normalise.
-- I hope the performance penalty is not big (since we are dealing with
-- l.h.s. terms only).
-- A systematic solution would make unification type-directed and
-- eta-insensitive...
--   liftTCM $ etaContract =<< reduce (applySubst rho u)

instance UReduce Type where
  ureduce (El s t) = El s <$> ureduce t

instance UReduce t => UReduce (HomHet t) where
  ureduce (Hom t)     = Hom <$> ureduce t
  ureduce (Het t1 t2) = Het <$> ureduce t1 <*> ureduce t2

instance UReduce t => UReduce (Maybe t) where
  ureduce Nothing = return Nothing
  ureduce (Just t) = Just <$> ureduce t

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
	Just u = s !! i

    inst :: Nat -> Term -> Term -> Term
    inst i u v = applySubst us v
      where us = [var j | j <- [0..i - 1] ] ++# u :# raiseS (i + 1)

data UnificationResult = Unifies Substitution | NoUnify Type Term Term | DontKnow TCErr

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

instance (Subst a) => Subst (HomHet a) where
  applySubst rho u = fmap (applySubst rho) u

instance (PrettyTCM a) => PrettyTCM (HomHet a) where
  prettyTCM (Hom a) = prettyTCM a
  prettyTCM (Het a1 a2) = prettyTCM a1 <+> text "||" <+> prettyTCM a2

type TermHH    = HomHet Term
type TypeHH    = HomHet Type
--type FunViewHH = FunV TypeHH
type TelHH     = Tele (I.Dom TypeHH)
type TelViewHH = TelV TypeHH

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

instance (Free a, Subst a) => SubstHH (HomHet a) (HomHet a) where
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

instance SubstHH a b => SubstHH (I.Arg a) (I.Arg b) where
  substUnderHH n u = fmap $ substUnderHH n u
  trivialHH = fmap trivialHH

instance SubstHH a b => SubstHH (I.Dom a) (I.Dom b) where
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
unifyIndices_ :: MonadTCM tcm => FlexibleVars -> Type -> [I.Arg Term] -> [I.Arg Term] -> tcm Substitution
unifyIndices_ flex a us vs = liftTCM $ do
  r <- unifyIndices flex a us vs
  case r of
    Unifies sub   -> return sub
    DontKnow err  -> throwError err
    NoUnify a u v -> typeError $ UnequalTerms CmpEq u v a

unifyIndices :: MonadTCM tcm => FlexibleVars -> Type -> [I.Arg Term] -> [I.Arg Term] -> tcm UnificationResult
unifyIndices flex a us vs = liftTCM $ do
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
      Left (ConstructorMismatch     a u v)  -> return $ NoUnify a u v
      -- Andreas 2011-04-14:
      Left (StronglyRigidOccurrence a u v)  -> return $ NoUnify a u v
      Left (GenericUnifyException     err)  -> fail err
      Right _                               -> do
        checkEqualities $ applySubst (makeSubstitution s) eqs
        let n = maximum $ (-1) : flex'
        return $ Unifies $ flattenSubstitution [ Map.lookup i s | i <- [0..n] ]
  `catchError` \err -> return $ DontKnow err
  where
    flex'      = map unArg flex
    flexible i = i `elem` flex'

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
      -> [I.Arg Term]  -- ^ the arguments of the constructor (lhs)
      -> [I.Arg Term]  -- ^ the arguments of the constructor (rhs)
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
         TelHH  -- ^ The telescope(s) of the constructor args    [length = n].
      -> [I.Arg Term]  -- ^ the arguments of the constructor (lhs) [length = n].
      -> [I.Arg Term]  -- ^ the arguments of the constructor (rhs) [length = n].
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
	, nest 2 $ text "at telescope" <+> prettyTCM bHH <+> text "..."
        ]
      liftTCM $ reportSDoc "tc.lhs.unify" 25 $
        (text $ "tel0 = " ++ show tel0)


      -- Andreas, Ulf, 2011-09-08 (AIM XIV)
      -- in case of dependent function type, we cannot postpone
      -- unification of u and v, otherwise us or vs might be ill-typed
      -- skip irrelevant parts
      uHH <- if isIrrelevant a then return $ Hom u else
               ifClean (unifyHH bHH u v) (return $ Hom u) (return $ Het u v)

      liftTCM $ reportSDoc "tc.lhs.unify" 25 $
        (text "uHH (before ureduce) =" <+> prettyTCM uHH)

      uHH <- traverse ureduce uHH

      liftTCM $ reportSDoc "tc.lhs.unify" 25 $
        (text "uHH (after  ureduce) =" <+> prettyTCM uHH)

      unifyConArgs (tel `absAppHH` uHH) us vs


    -- | Used for arguments of a 'Def', not 'Con'.
    unifyArgs :: Type -> [I.Arg Term] -> [I.Arg Term] -> Unify ()
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
	_	  -> __IMPOSSIBLE__
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

    unifySizes :: Term -> Term -> Unify ()
    unifySizes u v = do
      sz <- liftTCM sizeType
      su <- liftTCM $ sizeView u
      sv <- liftTCM $ sizeView v
      case (su, sv) of
        (SizeSuc u, SizeSuc v) -> unify sz u v
        (SizeSuc u, SizeInf) -> unify sz u v
        (SizeInf, SizeSuc v) -> unify sz u v
        _                    -> unifyAtom sz u v

    -- | Possibly heterogeneous unification (but at same-shaped types).
    --   In het. situations, we only search for a mismatch!
    --
    -- TODO: eta for records!
    unifyHH ::
        TypeHH  -- ^ one or two types, need not be in (u)reduced form
     -> Term -> Term -> Unify ()
    unifyHH aHH u v = do
      u <- liftTCM . constructorForm =<< ureduce u
      v <- liftTCM . constructorForm =<< ureduce v
      aHH <- ureduce aHH
      liftTCM $ reportSDoc "tc.lhs.unify" 15 $
	sep [ text "unifyHH"
	    , nest 2 $ (parens $ prettyTCM u) <+> text "=?="
	    , nest 2 $ parens $ prettyTCM v
	    , nest 2 $ text ":" <+> prettyTCM aHH
	    ]
      -- obtain the (== Size) function
      isSizeName <- liftTCM isSizeNameTest

      -- check whether types have the same shape
      (aHH, sh) <- shapeViewHH aHH
      case sh of
        ElseSh  -> checkEqualityHH aHH u v -- not a type or not same types

        DefSh d -> if isSizeName d then unifySizes u v
                                   else unifyAtomHH aHH u v
        _ -> unifyAtomHH aHH u v

    unifyAtomHH ::
         TypeHH -- ^ in ureduced form
      -> Term -> Term -> Unify ()
    unifyAtomHH aHH0 u v = do
      let (aHH, homogeneous, a) = case aHH0 of
            Hom a                -> (aHH0, True, a)
            Het a1 a2 | a1 == a2 -> (Hom a1, True, a1) -- BRITTLE: just checking syn.eq.
            _                    -> (aHH0, False, __IMPOSSIBLE__)
           -- use @a@ only if 'homogeneous' holds!

          fallback = checkEqualityHH aHH u v

      liftTCM $ reportSDoc "tc.lhs.unify" 15 $
	sep [ text "unifyAtom"
	    , nest 2 $ prettyTCM u <> if flexibleTerm u then text " (flexible)" else empty
            , nest 2 $ text "=?="
	    , nest 2 $ prettyTCM v <> if flexibleTerm v then text " (flexible)" else empty
	    , nest 2 $ text ":" <+> prettyTCM aHH
	    ]
      case (ignoreSharing u, ignoreSharing v) of
        -- Ulf, 2011-06-19
        -- We don't want to worry about levels here.
        (Level l, _) -> do
            u <- liftTCM $ reallyUnLevelView l
            unifyAtomHH aHH u v
        (_, Level l) -> do
            v <- liftTCM $ reallyUnLevelView l
            unifyAtomHH aHH u v
	(Var i us, Var j vs) | i == j  -> checkEqualityHH aHH u v
	(Var i [], _) | homogeneous && flexible i -> i |->> (v, a)
	(_, Var j []) | homogeneous && flexible j -> j |->> (u, a)
	(Con c us, Con c' vs)
          | c == c' -> do
              r <- ureduce =<< liftTCM (dataOrRecordTypeHH c aHH)
              case r of
                Just a'HH -> unifyConstructorArgs a'HH us vs
                Nothing   -> checkEqualityHH aHH u v
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
              inj <- liftTCM $ optInjectiveTypeConstructors <$> pragmaOptions
              if inj && ok
                then unifyArgs (defType def) us vs
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
            ok <- liftTCM $ instMeta a m us v
            liftTCM $ reportSDoc "tc.lhs.unify" 40 $
              vcat [ fsep [ text "inst meta", text $ if ok then "(ok)" else "(not ok)" ]
                   , nest 2 $ sep [ prettyTCM u, text ":=", prettyTCM =<< normalise u ]
                   ]
            if ok then unify a u v
                  else addEquality a u v
        (_, MetaV m vs) | homogeneous -> do
            ok <- liftTCM $ instMeta a m vs u
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

    unifyAtom :: Type -> Term -> Term -> Unify ()
    unifyAtom a = unifyAtomHH (Hom a)

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
            noConstraints $ assignV m us (v' `apply` margs)
            return True
          `catchError` \_ -> return False

    inertApplication :: Type -> Term -> TCM (Maybe (Term, Type, Args))
    inertApplication a v =
      case ignoreSharing v of
        Con c vs -> fmap (\ b -> (Con c [], b, vs)) <$> dataOrRecordType c a
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
dataOrRecordType
  :: QName -- ^ Constructor name.
  -> Type  -- ^ Type of constructor application (must end in data/record).
  -> TCM (Maybe Type) -- ^ Type of constructor, applied to pars.
dataOrRecordType c a = fmap (\ (d, b, args) -> b `apply` args) <$> dataOrRecordType' c a

dataOrRecordType' ::
     QName -- ^ Constructor name.
  -> Type  -- ^ Type of constructor application (must end in data/record).
  -> TCM (Maybe (QName, Type, Args))
           -- ^ Name of data/record type,
           --   type of constructor to be applied, and
           --   data/record parameters
dataOrRecordType' c a = do
  -- The telescope ends with a datatype or a record.
  (d, args) <- do
    TelV _ (El _ def) <- telView a
    let Def d args = ignoreSharing def
    return (d, args)
  def <- theDef <$> getConstInfo d
  r <- case def of
    Datatype{dataPars = n} -> Just . ((,) n) . defType <$> getConstInfo c
    Record  {recPars  = n} -> Just . ((,) n) <$> getRecordConstructorType d
    _		           -> return Nothing
  return $ fmap (\ (n, a') -> (d, a', genericTake n args)) r

-- | Heterogeneous situation.
--   @a1@ and @a2@ need to end in same datatype/record.
dataOrRecordTypeHH ::
     QName      -- ^ Constructor name.
  -> TypeHH     -- ^ Type(s) of constructor application (must end in same data/record).
  -> TCM (Maybe TypeHH) -- ^ Type of constructor, instantiated possibly heterogeneously to parameters.
dataOrRecordTypeHH c (Hom a) = fmap Hom <$> dataOrRecordType c a
dataOrRecordTypeHH c (Het a1 a2) = do
  r1 <- dataOrRecordType' c a1
  r2 <- dataOrRecordType' c a2  -- b2 may have different parameters than b1!
  return $ case (r1, r2) of
    (Just (d1, b1, pars1), Just (d2, b2, pars2)) | d1 == d2 -> Just $
        -- Andreas, 2011-09-15 if no parameters, we can stay homogeneous
        if null pars1 && null pars2 then Hom b1
         -- if parameters, go heterogeneous
         -- TODO: make this smarter, because parameters could be equal!
         else Het (b1 `apply` pars1) (b2 `apply` pars2)
    _ -> Nothing

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
  = PiSh (I.Dom a) (I.Abs a)
  | FunSh (I.Dom a) a
  | DefSh QName   -- ^ data/record
  | VarSh Nat     -- ^ neutral type
  | LitSh Literal -- ^ built-in type
  | SortSh
  | MetaSh        -- ^ some meta
  | ElseSh        -- ^ not a type or not definitely same shape
  deriving (Typeable, Show, Eq, Ord, Functor)

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
    FunSh a b -> absV a "_" <$> telViewUpToHH (n-1) (raise 1 b)
    _         -> return $ TelV EmptyTel t
  where
    absV a x (TelV tel t) = TelV (ExtendTel a (Abs x tel)) t
