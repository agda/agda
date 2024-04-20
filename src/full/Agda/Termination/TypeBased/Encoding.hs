{- | Contains utilities for translation of terms written in internal syntax to their sized counterparts.
     The translation is needed sincethe signatures of functions, constructors, projections and datatypes should be translated to sized types
     so the size-checking algorithm will be able to work with them.

    The translation itself is syntax-directed, though there are some complications
    since we are targeting a weaker theory than dependent types (our case is System Fω).
    One example of complication is the necessity to reduce certain definitions, which is undesirable in terms of performance.
    However, since all reductions occurr on type-level, we conjecture that the unfolded functions are not too heavy:
    it is unlikely that type alias carries non-trivial computational content.
 -}
{-# LANGUAGE NamedFieldPuns #-}
module Agda.Termination.TypeBased.Encoding
  ( encodeFieldType
  , encodeFunctionType
  , encodeBlackHole
  , encodeConstructorType
  ) where

import Control.Monad.State.Class ( gets, modify, MonadState )
import Control.Monad ( when, foldM )
import Control.Monad.Trans.State (StateT, runStateT)
import Data.Either ( fromRight )
import qualified Data.List as List
import Data.Maybe ( fromJust )
import qualified Data.Set as Set
import Data.Set ( Set )
import qualified Data.IntSet as IntSet

import Agda.Syntax.Abstract.Name ( QName )
import Agda.Syntax.Common ( Induction(..), Arg(unArg), HasEta' (..), HasEta )
import Agda.Syntax.Internal ( isApplyElim, Type, Type''(unEl), Abs(NoAbs, Abs, unAbs), Term(Var, Sort, MetaV, Lam, Pi, Def), Dom'(unDom) )
import Agda.Termination.TypeBased.Common ( applyDataType, tryReduceCopy, fixGaps, computeDecomposition, VariableInstantiation(..), reifySignature )
import Agda.Termination.TypeBased.Syntax ( SizeSignature(SizeSignature), SizeBound(SizeUnbounded, SizeBounded), FreeGeneric(..), SizeType(..), Size(SUndefined, SDefined), pattern UndefinedSizeType, sizeCodomain )
import Agda.TypeChecking.Monad.Base ( TCM, Definition(defCopy, defSizedType, theDef, defType), MonadTCM(liftTCM), pattern Record, recInduction, pattern Datatype, pattern Function, funTerminates, defIsDataOrRecord, EtaEquality(..), MonadTCEnv )
import Agda.TypeChecking.Monad.Debug ( MonadDebug, reportSDoc )
import Agda.TypeChecking.Monad.Signature ( HasConstInfo(getConstInfo) )
import Agda.TypeChecking.Pretty ( PrettyTCM(prettyTCM), pretty, (<+>), vcat, text )
import Agda.TypeChecking.Reduce ( instantiate, reduce )
import Agda.TypeChecking.Substitute ( TelV(TelV), telView' )
import Agda.Utils.Impossible ( __IMPOSSIBLE__ )
import Agda.TypeChecking.Monad.Context (AddContext(..), MonadAddContext)

-- | Converts internal type of function to a sized type
encodeFunctionType :: Type -> TCM SizeSignature
encodeFunctionType t = do
  EncodingResult { erNewFirstOrderVariables, erEncodedType } <- typeToSizeType 0 0 [] Nothing t
  -- Functions do not feature non-trivial size dependencies, hence we set all bounds to SizeUnbounded
  let newBounds = replicate erNewFirstOrderVariables SizeUnbounded
  let originalSignature = SizeSignature newBounds erEncodedType
  return $ fixGaps originalSignature

-- | 'encodeFieldType mutualNames t' converts internal type 't' of record projections to a sized type,
--   where 'mutualNames' is a set of names in a mutual block of the projected record.
--   For recursive record projections, the sizes of record occurrences in the codomain are smaller than the size of the record itself,
--   which is positioned as the principal parameter of the projection.
encodeFieldType :: Set QName -> Type -> TCM SizeSignature
encodeFieldType mutualNames t = do
  EncodingResult { erEncodedType, erNewFirstOrderVariables, erNewChosenInductiveVariables, erNewChosenCoInductiveVariables } <- ctorTypeToSizeType t mutualNames
  -- Since it is a projection, we know that the principal argument is the first withing the domain telescope.
  -- It means that the encoder contains it in the end of 'erNewChosenVariables', so we should reverse the list to get it.
  -- There is a similar discussion in 'encodeConstructorType'.
  bounds <- case reverse erNewChosenCoInductiveVariables of
    (principal : remaining) -> do
      reportSDoc "term.tbt" 80 $ "Chosen: " <+> text (show erNewChosenCoInductiveVariables)
      let bounds = map (\i -> if i `List.elem` remaining then SizeBounded principal else SizeUnbounded) [0..erNewFirstOrderVariables - 1]
      pure bounds
    [] -> pure $ (replicate erNewFirstOrderVariables SizeUnbounded)
  let sig = SizeSignature bounds erEncodedType
  reportSDoc "term.tbt" 20 $ "Sig: " <> pretty sig
  -- Record projections are always size-preserving in their inductive size.
  let amendedSig = case erNewChosenInductiveVariables of
        (x : rest) -> reifySignature (map (, ToVariable x) (List.sort rest)) sig
        [] -> sig
  pure amendedSig

-- | Converts an arbitrary type to a useless size signature
--   It is convenient to have sized types for all definitions in the project.
encodeBlackHole :: Type -> SizeSignature
encodeBlackHole t =
  let TelV domains codom = telView' t
  in SizeSignature [] $ foldr (\tp codom -> SizeArrow UndefinedSizeType codom) UndefinedSizeType domains

ctorTypeToSizeType :: Type -> Set QName -> TCM EncodingResult
ctorTypeToSizeType t qns = typeToSizeType 0 0 [] (Just (`Set.member` qns)) t

data EncodingResult = EncodingResult
  { erEncodedType :: SizeType
  -- ^ The result of conversion of an internal type to a sized type.
  , erNewFirstOrderVariables :: Int
  -- ^ The number of new first-order variables introduced during the conversion.
  , erNewChosenInductiveVariables :: [Int]
  -- ^ The list of new variables satisfying the passed 'esPredicate'.
  , erNewChosenCoInductiveVariables :: [Int]
  -- ^ The list of new variables satisfying the passed 'esPredicate'.
  }

data EncoderState = EncoderState
  { esVariableCounter        :: Int
  -- ^ Current pool of first-order variables
  , esTypeRelatedContext     :: [Maybe FreeGeneric]
  -- ^ Representation of the core context.
  --   'Nothing' means that the variable is "first-order", (like 'l : List'), hence its encoding should be 'UndefinedSizeType'.
  --   'Just x' means that the variable is "second-order", (like 'A : Set'), where 'x' is the index of corresponding generic.
  --   If the approach changes from System F to the dependent types, this field should be revised.
  , esTopLevel               :: Bool
  -- ^ Represents if encoding happens without any descend into higher-order functions.
  --   Essentially, this field regulates the behavior of the encoder on 'Set'.
  --   Motivation: Encoding of a signature 'A -> Set' should yield '∞ -> ∞' (since dangling generic variables are not expected in my approach),
  --   where encoding of '(A -> Set) -> Set' should yield 'Λ₁ε₀. ∞'.
  , esPredicate              :: Maybe (QName -> Bool)
  -- ^ A passed predicate, which is used to store some user's interesting variables.
  , esChosenInductiveVariables :: [Int]
  -- ^ List of variables that satisfy 'esPredicate' and correspond to least fixpoints.
  , esChosenCoInductiveVariables :: [Int]
  -- ^ List of variables that satisfy 'esPredicate' and correspond to greatest fixpoints.
  }

typeToSizeType :: Int -> Int -> [Maybe FreeGeneric] -> Maybe (QName -> Bool) -> Type -> TCM EncodingResult
typeToSizeType regVars genVars ctx pred t = case typeToSizeType' (unEl t) of
  ME action -> do
    (encodedType, finalEncoderState) <- runStateT action (EncoderState
      { esVariableCounter = regVars
      , esTypeRelatedContext = ctx
      , esTopLevel = True
      , esChosenInductiveVariables = []
      , esChosenCoInductiveVariables = []
      , esPredicate = pred
      })
    pure EncodingResult
      { erEncodedType = either __IMPOSSIBLE__ id encodedType
      , erNewFirstOrderVariables = esVariableCounter finalEncoderState
      , erNewChosenInductiveVariables = esChosenInductiveVariables finalEncoderState
      , erNewChosenCoInductiveVariables = esChosenCoInductiveVariables finalEncoderState
      }

newtype MonadEncoder a = ME (StateT EncoderState TCM a)
  deriving (Functor, Applicative, Monad, MonadDebug, MonadState EncoderState, MonadTCEnv, MonadAddContext)

-- | 'encodeConstructorType ind mutuals t' encodes a type 't' of constructor belonging to an inductive data definition,
--   where 'mutuals' is a set of names in a mutual block of the data definition and 'ind' is indication whether the defined mutual-recursive datatype is coinductive.
encodeConstructorType :: HasEta -> Induction -> Set QName -> Type -> TCM SizeSignature
encodeConstructorType eta ind mutuals t = do
  EncodingResult { erEncodedType, erNewFirstOrderVariables, erNewChosenInductiveVariables, erNewChosenCoInductiveVariables } <- ctorTypeToSizeType t mutuals

  -- We are trying to select variables that are located in the domain of the encoded constructor.
  -- Since each constructor has its datatype in the codomain, we know that the size variable for the codomain is added _last_,
  -- i.e. it is located in the beginning of the list of chosen variables (yeah, sounds like an abstraction leak, maybe TODO).
  let chosen = case erNewChosenInductiveVariables of
        (_ : x) -> x
        -- Black holes do not contain chosen variables, so there may be none of them.
        [] -> []
  let chosenCoind = case erNewChosenCoInductiveVariables of
        (_ : x) -> x
        [] -> []
  let (SizeTree indSize coindSize _) = snd $ sizeCodomain erEncodedType
  let sizeToBound s = case s of
        SUndefined -> SizeUnbounded
        SDefined i -> SizeBounded i
  reportSDoc "term.tbt" 60 $ vcat
    [ "Chosen variables: " <+> text (show erNewChosenInductiveVariables)
    , "Chosen coinductive: " <+> text (show erNewChosenCoInductiveVariables)
    ]
  let bounds = map (\i -> if i `elem` chosen then sizeToBound indSize else SizeUnbounded) [0..erNewFirstOrderVariables - 1]
  let signature = SizeSignature bounds erEncodedType
  reportSDoc "term.tbt" 60 $ "Original signature: " <+> pretty signature
  let adjustedSignature = case ind of
        Inductive -> case eta of
          YesEta ->
            -- Issue #7206, constructors of records with eta equality should not be size-decreasing
            let (SDefined principalInd) = indSize
            in reifySignature (List.sortOn fst $ map (, ToVariable principalInd) chosen) signature
          NoEta _ -> signature
        CoInductive ->
          let (SDefined principalCoind) = coindSize
          in reifySignature (List.sortOn fst $ map (, ToVariable principalCoind) chosenCoind) signature
  reportSDoc "term.tbt" 60 $ "Adjusted signature: " <+> pretty adjustedSignature
  pure $ adjustedSignature

typeToSizeType' :: Term -> MonadEncoder (Either FreeGeneric SizeType)
typeToSizeType' (Sort _) = do
  tl <- gets esTopLevel
  if tl
  then pure $ Right UndefinedSizeType
  else pure $ Left (FreeGeneric 0 0)
typeToSizeType' t@(Pi dom cod) = do

  domEncoding <- freezeContext $ typeToSizeType' $ unEl $ unDom dom
  enrichContext domEncoding cod

  codomEncoding <- addContext ("_" :: String, dom) $ typeToSizeType' $ unEl $ unAbs cod
  combinedType <- case (domEncoding, codomEncoding) of
        (_, Left fg) -> do
          -- Since we are trying to build a generic with arity, its arity increases with the introduction of domain.
          pure $ Left (fg { fgArity = fgArity fg + 1})
        (Left fg, Right tele) ->
          -- The domain initiates generic parameterization, hence we need to create a second-order parameterized type
          pure $ Right $ SizeGeneric (fgArity fg) tele
        (Right realDomain, Right realCodomain) ->
          -- If there is no requirement to handle generics, we can construct a plain arrow type.
          pure $ Right $ SizeArrow realDomain realCodomain
  reportSDoc "term.tbt" 50 $ vcat
    [ "Converted term: " <+> prettyTCM t
    , "partial type: " <+> pretty combinedType
    ]
  pure combinedType
typeToSizeType' t@(MetaV _ _) = do
  reportSDoc "term.tbt" 80 $ "Preparing to instantiate meta"
  inst <- ME $ instantiate t
  case inst of
    MetaV _ _ -> pure $ Right $ UndefinedSizeType
    t -> typeToSizeType' t
typeToSizeType' t@(Lam _ abs) = do
  -- Here we "lift" lambda expressions to the type level, thus obtaining an arrow type.
  -- The purpose of this trick is to respect the arity of generic to which this lambda is applied.
  -- Example:
  -- Assume that we are given a function 'foo : Λ₁ε₁ -> ₁ε₁ -> ...'
  -- And we are processing an application 'foo (λ p → List Nat)'
  -- With the conversion of lambdas, we will obtain instantiation of "ε₁ => ∞ -> t₁<...>", where t₁ is the representation of List.
  -- Later, we will be able to track the termination of the argument of type ₁ε₁.
  reportSDoc "term.tbt" 60 $ "Converting lambda" <+> prettyTCM t
  let isAbs = case abs of
        Abs _ _ -> True
        NoAbs _ _ -> False
  when isAbs $ modify (\s -> s { esTypeRelatedContext = Nothing : esTypeRelatedContext s })
  sizeCod <- typeToSizeType' (unAbs abs)
  pure $ case sizeCod of
    Left fg -> Left (fg { fgArity = fgArity fg + 1 })
    Right tele -> Right $ SizeArrow UndefinedSizeType tele
typeToSizeType' t@(Def qn _) = do
  reportSDoc "term.tbt" 60 $ "Converting def" <+> prettyTCM t
  constInfo <- ME $ getConstInfo qn
  let dataHandler = Right <$> (termToSizeType =<< ME (liftTCM (tryReduceCopy t)))
  case theDef constInfo of
    -- A function usage in the signature might be a type alias, which means that we have to unfold it
    -- to get the full signature to encode.
    -- It also may be the case that there are several level of indirections until actual set-valued signature,
    -- so we are trying to unconditionally unfold every definition.
    Function{ funTerminates } | funTerminates == Just True -> do
      reduced <- ME $ reduce t
      reportSDoc "term.tbt" 60 $ vcat
        [ "Unfolded: " <+> prettyTCM t
        , "to: " <+> prettyTCM reduced
        ]
      case reduced of
        Pi _ _ -> typeToSizeType' reduced
        Def qn' _ | qn' /= qn -> typeToSizeType' reduced -- non-trivial unfolding occurred
        _ -> pure $ Right $ UndefinedSizeType
    Datatype{} -> dataHandler
    Record{} -> dataHandler
    _ -> pure $ Right UndefinedSizeType
typeToSizeType' r = Right <$> termToSizeType r

enrichContext :: Either FreeGeneric SizeType -> Abs a -> MonadEncoder ()
enrichContext (Left fg) (Abs _ _) = modify (\s -> s { esTypeRelatedContext = Just fg : (map (fmap increaseIndexing) (esTypeRelatedContext s)) })
enrichContext _ (Abs _ _) = modify (\s -> s { esTypeRelatedContext = Nothing : esTypeRelatedContext s })
enrichContext (Left fg) (NoAbs _ _) = modify (\s -> s { esTypeRelatedContext = map (fmap increaseIndexing) (esTypeRelatedContext s) })
enrichContext _ _ = pure ()

increaseIndexing :: FreeGeneric -> FreeGeneric
increaseIndexing fg = fg { fgIndex = fgIndex fg + 1 }

-- | Converts a datatype to its size representation. The result is most likely size tree (i.e. t₃<∞, ∞, ∞>)
termToSizeType :: Term -> MonadEncoder SizeType
termToSizeType t@(Def q elims) = do
  constInfo <- ME $ getConstInfo q
  let (SizeSignature _ tele) = defSizedType constInfo
  if defIsDataOrRecord (theDef constInfo) then do
    reportSDoc "term.tbt" 80 $ "Converting to size tree: " <+> prettyTCM t <+> ", elims: " <+> (prettyTCM elims)
    -- Datatypes have parameters, which also should be converted to size types.
    dataArguments <- map (fromRight UndefinedSizeType) <$> traverse (freezeContext . typeToSizeType' . unArg . fromJust . isApplyElim) elims

    freshData <- refreshFirstOrder tele
    reportSDoc "term.tbt" 80 $ vcat
      [ "Applying elims to: " <+> pretty freshData
      , "elims: " <+> pretty dataArguments
      , "actual term: " <+> prettyTCM t
      , "actual type: " <+> prettyTCM (defType constInfo)
      , "copy: " <+> (text (show (defCopy constInfo)))
      ]
    let newTree = applyDataType dataArguments freshData
    reportSDoc "term.tbt" 60 $ "Resulting tree: " <+> pretty newTree <+> "for" <+> prettyTCM t
    predicate <- gets esPredicate
    collectChosenVariables predicate newTree
  else do
    reportSDoc "term.tbt" 80 $ "Aborting conversion of " <+> prettyTCM q
    return UndefinedSizeType -- arbitraty function applications in signatures are not supported on the current stage
  where
    collectChosenVariables :: Maybe (QName -> Bool) -> SizeType -> MonadEncoder SizeType
    collectChosenVariables predicate t@(SizeTree d1 d2 rest) = do
      case predicate of
        Just p | not (p q) -> do
          pure (SizeTree SUndefined SUndefined rest)
        _ -> do
          let (l1, l2) = case (d1, d2) of
                (SUndefined, SUndefined) -> ([], [])
                (SDefined i, SUndefined) -> ([i], [])
                (SUndefined, SDefined i) -> ([], [i])
                (SDefined i, SDefined j) -> ([i], [j])
          modify (\s -> s { esChosenInductiveVariables = l1 ++ esChosenInductiveVariables s, esChosenCoInductiveVariables = l2 ++ esChosenCoInductiveVariables s } )
          pure t
    collectChosenVariables p (SizeArrow l r) = SizeArrow l <$> collectChosenVariables p r
    collectChosenVariables p (SizeGeneric e r) = SizeGeneric e <$> collectChosenVariables p r
    collectChosenVariables _ t = pure t

    -- Freshens all first-order variables in an encoded type
    refreshFirstOrder ::  SizeType -> MonadEncoder SizeType
    refreshFirstOrder s@(SizeGeneric args r) = SizeGeneric args <$> refreshFirstOrder r
    refreshFirstOrder s@(SizeArrow l r) = SizeArrow <$> (refreshFirstOrder l) <*> (refreshFirstOrder r)
    refreshFirstOrder s@(SizeGenericVar args i) = pure s
    refreshFirstOrder s@(SizeTree d1 d2 ts) = SizeTree <$> (case d1 of
      SDefined i -> SDefined <$> initNewFirstOrderInEncoder
      SUndefined -> pure SUndefined) <*> (case d2 of
      SDefined i -> SDefined <$> initNewFirstOrderInEncoder
      SUndefined -> pure SUndefined) <*> traverse (\(p, t) -> (p,) <$> refreshFirstOrder t) ts
termToSizeType (Var varId elims) = do
    ctx <- gets esTypeRelatedContext
    reportSDoc "term.tbt" 60 $ vcat
      [ "Context before var" <+> pretty ctx
      , "var: " <+> text (show varId)
      ]
    case ctx List.!! varId of
      Nothing -> pure $ UndefinedSizeType
      Just fg -> pure $ SizeGenericVar (length elims) (fgIndex fg)
termToSizeType _ = pure UndefinedSizeType

-- | Returns new first-order size variable in the encoder monad
initNewFirstOrderInEncoder :: MonadEncoder Int
initNewFirstOrderInEncoder = do
  variableIndex <- ME $ gets esVariableCounter
  ME $ modify (\s -> s
    { esVariableCounter = esVariableCounter s + 1
    })
  -- when contra $ modify (\s -> s { esContravariantVariables = variableIndex : esContravariantVariables s })
  pure variableIndex

-- | Performs an action and rollbacks the context afterwards.
freezeContext :: MonadEncoder a -> MonadEncoder a
freezeContext action = do
  ctx <- ME $ gets esTypeRelatedContext
  tl <- ME $ gets esTopLevel
  ME $ modify (\s -> s { esTopLevel = False })
  res <- action
  ME $ modify (\s -> s {esTypeRelatedContext = ctx, esTopLevel = tl})
  return res
