{- | Contains utilities for translation of terms written in internal syntax to their sized counterparts.
     The translation is needed in two places:
     1) The signatures of functions, constructors, projections and datatypes should be translated to sized types
        so the size-checking algorithm will be able to work with them.
     2) Since types are first-class citizens in Agda's theory, it is the case that there are type applications in the internal syntax.
        To hangle type applications, we need to translate certain terms to sized types during the checking, and then do some sort of application.
        This is covered under the terms of generics, unification and instantiation.

    The translation itself is syntax-directed, though there are some complications
    since we are targeting a weaker theory than dependent types (our case is System Fω).
    One example of complication is the necessity to reduce certain definitions, which is undesirable in terms of performance.
    However, since all reductions occurr on type-level, we conjecture that the unfolded functions are not too heavy:
    it is unlikely that type alias carries non-trivial computational content.
 -}
{-# LANGUAGE NamedFieldPuns #-}
module Agda.Termination.TypeBased.Encoding where

import Control.Monad.Trans.State (StateT, runStateT)
import Agda.Syntax.Abstract.Name
import Agda.Syntax.Internal
import Agda.Syntax.Common
import Agda.Termination.TypeBased.Syntax
import Agda.Termination.TypeBased.Common
import Agda.TypeChecking.Substitute
import Agda.TypeChecking.Monad.Base
import Agda.TypeChecking.Monad.Debug
import Agda.TypeChecking.Monad.Signature
import Agda.TypeChecking.Pretty
import Agda.TypeChecking.Reduce
import qualified Data.Set as Set
import Data.Set ( Set )
import Control.Monad ( when, foldM )
import qualified Data.List as List
import Data.Maybe ( fromJust )
import Agda.Termination.TypeBased.Common ( applyDataType )
import Control.Monad.State.Class

-- | Converts internal type of function to a sized type
encodeFunctionType :: Type -> TCM SizeSignature
encodeFunctionType t = do
  EncodingResult { erNewFirstOrderVariables, erNewContravariantVariables, erEncodedType } <- typeToSizeTele 0 0 [] (const False) t
  -- Functions do not feature non-trivial size dependencies, hence we set all bounds to SizeUnbounded
  let newBounds = (replicate erNewFirstOrderVariables SizeUnbounded)
  return $ SizeSignature newBounds erNewContravariantVariables erEncodedType

-- | 'encodeFieldType mutualNames t' converts internal type 't' of record projections to a sized type,
--   where 'mutualNames' is a set of names in a mutual block of the projected record.
--   For recursive record projections, the sizes of record occurrences in the codomain are smaller than the size of the record itself,
--   which is positioned as the principal parameter of the projection.
encodeFieldType :: Set QName -> Type -> TCM SizeSignature
encodeFieldType mutualNames t = do
  EncodingResult { erEncodedType, erNewFirstOrderVariables, erNewContravariantVariables, erNewChosenVariables } <- ctorTypeToSizeTele t mutualNames
  -- Since it is a projection, we know that the principal argument is the first withing the domain telescope.
  -- It means that the encoder contains it in the end of 'erNewChosenVariables', so we should reverse the list to get it.
  -- There is a similar discussion in 'encodeConstructorType'.
  bounds <- case reverse erNewChosenVariables of
    (principal : remaining) -> do
      reportSDoc "term.tbt" 20 $ "Chosen: " <+> text (show erNewChosenVariables)
      let bounds = map (\i -> if i `List.elem` remaining then SizeBounded principal else SizeUnbounded) [0..erNewFirstOrderVariables - 1]
      pure bounds
    [] -> pure $ (replicate erNewFirstOrderVariables SizeUnbounded)
  pure $ SizeSignature bounds erNewContravariantVariables erEncodedType

-- | Converts an arbitrary type to a useless size signature
--   It is convenient to have sized types for all definitions in the project.
--   However, if there is no `--type-based-termination` enabled in a file,
--   we should not do non-trivial computations with the processed definitions.
encodeBlackHole :: Type -> SizeSignature
encodeBlackHole t =
  let TelV domains codom = telView' t
  in SizeSignature [] [] $ foldr (\tp codom -> SizeArrow (SizeTree SUndefined []) codom) UndefinedSizeTele domains

ctorTypeToSizeTele :: Type -> Set QName -> TCM EncodingResult
ctorTypeToSizeTele t qns = typeToSizeTele 0 0 [] (`Set.member` qns) t

data EncodingResult = EncodingResult
  { erEncodedType :: SizeTele
  -- ^ The result of conversion of an internal type to a sized type.
  , erNewFirstOrderVariables :: Int
  -- ^ The number of new first-order variables introduced during the conversion.
  , erNewGenericArities :: [Int]
  -- ^ The arities of new generic variables introduced during the conversion. The number of new generic variables is implicitly the length of this list
  , erNewChosenVariables :: [Int]
  -- ^ The list of new variables satisfying the passed 'esPredicate'.
  , erNewContravariantVariables :: [Int]
  -- ^ The list of new contravariant variables introduced during the conversion
  }

data EncoderState = EncoderState
  { esVariableCounter        :: Int
  -- ^ Current pool of first-order variables
  , esInitialGenericCounter  :: Int
  -- ^ Initial offset of generic variables. New generics are created starting from this offset.
  , esNewGenericArities      :: [Int]
  -- ^ Current list of generic arities.
  , esTypeRelatedContext     :: [Maybe Int]
  -- ^ Representation of the core context.
  --   'Nothing' means that the variable is "first-order", (like 'l : List'), hence its encoding should be 'UndefinedSizeTele'.
  --   'Just x' means that the variable is "second-order", (like 'A : Set'), where 'x' is the index of corresponding generic.
  --   If the approach changes from System F to the dependent types, this field should be revised.
  , esTopLevel               :: Bool
  -- ^ Represents if encoding happens without any descend into higher-order functions.
  --   Essentially, this field regulates the behavior of the encoder on 'Set'.
  --   Motivation: Encoding of a signature 'A -> Set' should yield '∞ -> ∞' (since dangling generic variables are not expected in my approach),
  --   where encoding of '(A -> Set) -> Set' should yield 'Λ₁ε₀. ∞'.
  , esPredicate              :: QName -> Bool
  -- ^ A passed predicate, which is used to store some user's interesting variables.
  , esChosenVariables        :: [Int]
  -- ^ List of variables that satisfy 'esPredicate'.
  , esContravariantVariables :: [Int]
  -- ^ Contravariant size variables collected during the encoding.
  }

typeToSizeTele :: Int -> Int -> [Maybe Int] -> (QName -> Bool) -> Type -> TCM EncodingResult
typeToSizeTele regVars genVars ctx pred t = case typeToSizeTele' (unEl t) of
  ME action -> do
    (encodedType, finalEncoderState) <- runStateT action (EncoderState
      { esVariableCounter = regVars
      , esInitialGenericCounter = genVars
      , esNewGenericArities = []
      , esTypeRelatedContext = ctx
      , esTopLevel = True
      , esChosenVariables = []
      , esPredicate = pred
      , esContravariantVariables = []
      })
    pure EncodingResult
      { erEncodedType = encodedType
      , erNewFirstOrderVariables = esVariableCounter finalEncoderState
      , erNewGenericArities = esNewGenericArities finalEncoderState
      , erNewChosenVariables = esChosenVariables finalEncoderState
      , erNewContravariantVariables = esContravariantVariables finalEncoderState
      }


newtype MonadEncoder a = ME (StateT EncoderState TCM a)
  deriving (Functor, Applicative, Monad, MonadDebug, MonadState EncoderState)

-- | 'encodeConstructorType mutuals t' encodes a type 't' of constructor belonging to an inductive data definition,
--   where 'mutuals' is a set of names in a mutual block of the data definition.
encodeConstructorType :: Set QName -> Type -> TCM SizeSignature
encodeConstructorType mutuals t = do
  EncodingResult { erEncodedType, erNewFirstOrderVariables, erNewChosenVariables, erNewContravariantVariables } <- ctorTypeToSizeTele t mutuals

  -- We are trying to select variables that are located in the domain of the encoded constructor.
  -- Since each constructor has its datatype in the codomain, we know that the size variable for the codomain is added _last_,
  -- i.e. it is located in the beginning of the list of chosen variables (yeah, sounds like an abstraction leak, maybe TODO).
  let chosen = case erNewChosenVariables of
        (_ : x) -> x
        -- Black holes do not contain chosen variables, so there may be none of them.
        [] -> []
  let (_, (SizeTree (SDefined principal) _)) = sizeCodomain erEncodedType
  reportSDoc "term.tbt" 20 $ "Chosen: " <+> text (show esChosenVariables)
  let bounds = map (\i -> if i `elem` chosen then (SizeBounded principal) else SizeUnbounded) [0..erNewFirstOrderVariables - 1]
  return $ SizeSignature bounds erNewContravariantVariables erEncodedType

typeToSizeTele' :: Term -> MonadEncoder SizeTele
typeToSizeTele' (Sort _) = do
  tl <- gets esTopLevel
  if tl
  then pure UndefinedSizeTele
  else do
    genericIndex <- initNewGenericInEncoder 0
    return $ StoredGeneric 0 genericIndex
typeToSizeTele' t@(Pi dom cod) = do

  domEncoding <- freezeContext $ typeToSizeTele' $ unEl $ unDom dom
  enrichContext domEncoding cod

  codomEncoding <- typeToSizeTele' $ unEl $ unAbs cod
  combinedType <- case (domEncoding, codomEncoding) of
        (_, StoredGeneric args i) -> do
          -- Here we are trying to build a generic with arity, its telescope should be collapsed to the arity integer.
          initialIndex <- ME $ gets esInitialGenericCounter
          modify (\s -> s { esNewGenericArities = listSet (i - initialIndex) (args + 1) (esNewGenericArities s)})
          pure $ StoredGeneric (args + 1) i
        (StoredGeneric args i, _) ->
          -- The domain initiates generic parameterization, hence we need to create a second-order parameterized type
          pure $ SizeGeneric args i codomEncoding
        (_, _) ->
          -- If there is no requirement to handle generics, we can construct a plain arrow type.
          pure $ SizeArrow domEncoding codomEncoding
  reportSDoc "term.tbt" 100 $ vcat
    [ "Converted term: " <+> prettyTCM t
    , "partial type: " <+> text (show combinedType)
    ]
  pure combinedType
typeToSizeTele' t@(MetaV _ _) = do
  reportSDoc "term.tbt" 20 $ "Preparing to instantiate meta"
  inst <- ME $ instantiate t
  case inst of
    MetaV _ _ -> pure UndefinedSizeTele
    t -> typeToSizeTele' t
typeToSizeTele' t@(Lam _ abs) = do
  -- Here we "lift" lambda expressions to the type level, thus obtaining an arrow type.
  -- The purpose of this trick is to respect the arity of generic to which this lambda is applied.
  -- Example:
  -- Assume that we are given a function 'foo : Λ₁ε₁ -> ₁ε₁ -> ...'
  -- And we are processing an application 'foo (λ p → List Nat)'
  -- With the conversion of lambdas, we will obtain instantiation of "ε₁ => ∞ -> t₁<...>", where t₁ is the representation of List.
  -- Later, we will be able to track the termination of the argument of type ₁ε₁.
  reportSDoc "term.tbt" 20 $ "Converting lambda" <+> prettyTCM t
  let isAbs = case abs of
        Abs _ _ -> True
        NoAbs _ _ -> False
  when isAbs $ modify (\s -> s { esTypeRelatedContext = Nothing : esTypeRelatedContext s })
  sizeCod <- typeToSizeTele' (unAbs abs)
  pure $ SizeArrow UndefinedSizeTele sizeCod
typeToSizeTele' t@(Def qn _) = do
  constInfo <- ME $ getConstInfo qn
  let dataHandler = termToSizeTele =<< ME (liftTCM (tryReduceCopy t))
  case theDef constInfo of
    -- A function usage in the signature might be a type alias, which means that we have to unfold it
    -- to get the full signature to encode.
    -- It also may be the case that there are several level of indirections until actual set-valued signature,
    -- so we are trying to unconditionally unfold every definition.
    Function{ funTerminates } | funTerminates == Just True -> do
      reduced <- ME $ reduce t
      reportSDoc "term.tbt" 20 $ vcat
        [ "Unfolding: " <+> prettyTCM t
        , "to: " <+> prettyTCM reduced
        ]
      case reduced of
        Pi _ _ -> typeToSizeTele' reduced
        Def qn' _ | qn' /= qn -> typeToSizeTele' reduced -- non-trivial unfolding occurred
        _ -> pure UndefinedSizeTele
    Datatype{} -> dataHandler
    Record{} -> dataHandler
    _ -> pure UndefinedSizeTele
typeToSizeTele' r = termToSizeTele r

enrichContext :: SizeTele -> Abs a -> MonadEncoder ()
enrichContext (StoredGeneric _ i) (Abs _ _) = modify (\s -> s { esTypeRelatedContext = Just i : esTypeRelatedContext s })
enrichContext _ (Abs _ _) = modify (\s -> s { esTypeRelatedContext = Nothing : esTypeRelatedContext s })
enrichContext _ _ = pure ()

-- | Converts a datatype to its size representation. The result is most likely size tree (i.e. t₃<∞, ∞, ∞>)
termToSizeTele :: Term -> MonadEncoder SizeTele
termToSizeTele t@(Def q elims) = do
  constInfo <- ME $ getConstInfo q
  let sig = defSizedType constInfo
  case sig of
    Just (SizeSignature _ _ tele) | defIsDataOrRecord (theDef constInfo) -> do
      reportSDoc "term.tbt" 20 $ "Raw term: " <+> prettyTCM t <+> ", elims: " <+> (prettyTCM elims)
      -- Datatypes have parameters, which also should be converted to size types.
      dataArguments <- traverse (freezeContext . typeToSizeTele' . unArg . fromJust . isApplyElim) elims

      freshData <- refreshFirstOrder tele
      reportSDoc "term.tbt" 20 $ vcat
        [ "Applying elims to: " <+> (text $ show freshData)
        , "elims: " <+> (text $ show $ reverse $ dataArguments)
        , "actual term: " <+> (prettyTCM t)
        , "actual type: " <+> (prettyTCM (defType constInfo))
        , "copy: " <+> (text (show (defCopy constInfo)))
        ]
      let newTree = applyDataType dataArguments freshData
      reportSDoc "term.tbt" 20 $ "Resulting tree: " <+> (text (show newTree)) <+> "for" <+> prettyTCM t
      predicate <- gets esPredicate
      case newTree of
        SizeTree (SDefined i) _ -> do
          when (predicate q) $ modify (\s -> s { esChosenVariables = i : esChosenVariables s} )
          case theDef constInfo of
            Record { recInduction } -> when (recInduction == Just CoInductive) $ modify (\s -> s { esContravariantVariables = i : esContravariantVariables s })
            _ -> pure ()
        _ -> pure ()
      pure newTree
    _ -> do
      reportSDoc "term.tbt" 20 $ "Aborting conversion of " <+> prettyTCM q
      return UndefinedSizeTele -- arbitraty function applications in signatures are not supported on the current stage
  where
    -- Freshens all first-order variables in an encoded type
    refreshFirstOrder :: SizeTele -> MonadEncoder SizeTele
    refreshFirstOrder s@(SizeGeneric args i r) = SizeGeneric args i <$> refreshFirstOrder r
    refreshFirstOrder s@(SizeArrow l r) = SizeArrow <$> (refreshFirstOrder l) <*> (refreshFirstOrder r)
    refreshFirstOrder s@(SizeGenericVar args i) = pure s
    refreshFirstOrder s@(SizeTree d ts) = SizeTree <$> (case d of
      SDefined i -> SDefined <$> initNewFirstOrderInEncoder
      SUndefined -> pure SUndefined) <*> traverse refreshFirstOrder ts
termToSizeTele (Var varId elims) = do
    ctx <- gets esTypeRelatedContext
    reportSDoc "term.tbt" 40 $ vcat
      [ "Context before var" <+> text (show ctx)
      , "var: " <+> text (show varId)
      ]
    case ctx List.!! varId of
      Nothing -> pure $ SizeTree SUndefined []
      Just i -> pure $ SizeGenericVar (length elims) i
termToSizeTele _ = pure UndefinedSizeTele

-- | Returns new generic variable in the encoder monad
initNewGenericInEncoder :: Int -> MonadEncoder Int
initNewGenericInEncoder arity = do
  offset <- ME $ gets esInitialGenericCounter
  genericIndex <- ME $ (+ offset) . length <$> gets esNewGenericArities
  ME $ modify (\s -> s
    { esNewGenericArities = arity : esNewGenericArities s
    })
  pure genericIndex

-- | Returns new first-order size variable in the encoder monad
initNewFirstOrderInEncoder :: MonadEncoder Int
initNewFirstOrderInEncoder = do
  variableIndex <- ME $ gets esVariableCounter
  ME $ modify (\s -> s
    { esVariableCounter = esVariableCounter s + 1
    })
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


listSet :: Int -> a -> [a] -> [a]
listSet 0 x (_ : ls) = x : ls
listSet n x (y : ys) = y : listSet (n - 1) x ys
listSet _ _ _ = error "bad listSet"
