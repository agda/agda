{-# LANGUAGE CPP #-}
{-# LANGUAGE NondecreasingIndentation #-}

module Agda.TypeChecking.Generalize (generalizeType) where

import Control.Arrow ((***))
import Control.Monad
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Map (Map)
import qualified Data.Map as Map
import Data.List (nub, partition, init)

import Agda.Syntax.Common
import Agda.Syntax.Position
import Agda.Syntax.Internal
import Agda.Syntax.Literal
import Agda.TypeChecking.Monad
import Agda.TypeChecking.Abstract
import Agda.TypeChecking.Constraints
import Agda.TypeChecking.Conversion
import Agda.TypeChecking.Irrelevance
import Agda.TypeChecking.MetaVars
import Agda.TypeChecking.Pretty
import Agda.TypeChecking.Reduce
import Agda.TypeChecking.Substitute
import Agda.TypeChecking.Telescope

import Agda.Utils.Functor
import Agda.Utils.Impossible
import Agda.Utils.Lens
import Agda.Utils.Maybe
import Agda.Utils.Size
import Agda.Utils.Permutation
import qualified Agda.Utils.Graph.TopSort as Graph

#include "undefined.h"

-- | Generalize a type over a set of (used) generalizable variables.
generalizeType :: Set QName -> TCM Type -> TCM (Int, Type)
generalizeType s typecheckAction = do

    -- Create a meta type (in Setω) for the telescope record
    genRecMeta <- newTypeMeta Inf
    let gt = "genTel" :: String

    addContext (defaultDom (gt, genRecMeta)) $ do

    (t, allmetas) <- metasCreatedBy $ do
      -- Create metas for all used generalizable variables and their dependencies.
      genvals <- fmap Map.fromList $ locallyTC eGeneralizeMetas (const YesGeneralize)
                                   $ forM (Set.toList s) createGenValue
      -- Check the type
      locallyTC eGeneralizedVars (const genvals) typecheckAction

    -- Pair metas with their metaInfo
    mvs <- mapM (\ x -> (x,) <$> lookupMeta x) (Set.toList allmetas)

    let isGeneralizable (_, mv) = YesGeneralize == unArg (miGeneralizable (mvInfo mv))
        isOpen = isOpenMeta . mvInstantiation . snd

    -- Split the generalizable metas in open and closed
    let (generalizable, nongeneralizable) = partition isGeneralizable mvs
        (generalizableOpen, generalizableClosed) = partition isOpen generalizable
        nongeneralizableOpen = filter isOpen nongeneralizable

    -- Any meta in the solution of a generalizable meta should be generalized over.
    cp <- viewTC eCurrentCheckpoint
    let canGeneralize x = do
            mv  <- lookupMeta x
            (mcp, sub) <- enterClosure (miClosRange $ mvInfo mv) $ \ _ ->
              (,) <$> viewTC eCurrentCheckpoint <*> checkpointSubstitution cp
            -- TODO: might pruned further
            let sameContext =
                  -- Do we have a weakening substitution and a corresponding
                  -- pruning getting rid of the extra variables?
                  case (sub, mvPermutation mv) of
                    (Wk n IdS, Perm m xs) -> xs == [0 .. m - n - 1]
                    _                     -> False
            when (mcp /= cp && not sameContext) $ do
              ty <- getMetaType x
              let Perm m xs = mvPermutation mv
              reportSDoc "tc.decl.gen" 20 $ vcat
                [ text "Not clear how to generalize over"
                , nest 2 $ prettyTCM x <+> text ":" <+> prettyTCM ty
                , text "in context"
                , nest 2 $ inTopContext . prettyTCM =<< getContextTelescope
                , text "permutation:" <+> text (show (m, xs))
                , text "subst:" <+> pretty sub ]
            return (mcp == cp || sameContext)
    inherited <- fmap Set.unions $ forM generalizableClosed $ \ (x, mv) ->
      case mvInstantiation mv of
        InstV _ v -> Set.fromList <$> (filterM canGeneralize . allMetas =<< instantiateFull v)
        _ -> __IMPOSSIBLE__

    let (alsoGeneralize, reallyDontGeneralize) = partition (`Set.member` inherited) $ map fst nongeneralizableOpen
        generalizeOver = map fst generalizableOpen ++ alsoGeneralize

    -- For now, we don't handle unsolved non-generalizable metas.
    -- unless (null reallyDontGeneralize) $
    --   typeError $ NotImplemented "Unsolved non-generalizable metas in generalized type"

    -- Sort metas in dependency order
    sortedMetas <- sortMetas generalizeOver

    reportSDoc "tc.decl.gen" 50 $ vcat
      [ text $ "allMetas    = " ++ show allmetas
      , text $ "sortedMetas = " ++ show sortedMetas ]

    let dropCxt err = updateContext (strengthenS err 1) (drop 1)

    -- Create the pre-record type (we don't yet know the types of the fields)
    (genRecName, genRecCon, genRecFields) <- dropCxt __IMPOSSIBLE__ $
        createGenRecordType genRecMeta sortedMetas

    -- Solve the generalizable metas
    let solve m field = do
          HasType _ a <- mvJudgement <$> lookupMeta m
          TelV tel _  <- telView a
          assignTerm' m (telToArgs tel) $ Var 0 [Proj ProjSystem field]
    zipWithM_ solve sortedMetas genRecFields

    -- Build the telescope of generalized metas
    teleTypes <- fmap concat $ forM sortedMetas $ \ m -> do
                    mv   <- lookupMeta m
                    args <- getContextArgs
                    let info = getArgInfo $ miGeneralizable $ mvInfo mv
                        HasType{ jMetaType = t } = mvJudgement mv
                    return [(Arg info $ miNameSuggestion $ mvInfo mv, piApply t args)]
    let genTel = buildGeneralizeTel genRecCon teleTypes
    reportSDoc "tc.decl.gen" 40 $ vcat
      [ text "genTel =" <+> prettyTCM genTel ]

    -- Fill in the missing details of the telescope record.
    dropCxt __IMPOSSIBLE__ $ fillInGenRecordDetails genRecName genRecCon genRecFields genRecMeta genTel

    -- Now abstract over the telescope
    let sub = unpackSub genRecCon (map (argInfo . fst) teleTypes) (length teleTypes)
    t' <- abstract genTel . applySubst sub <$> instantiateFull t

    reportSDoc "tc.decl.gen" 40 $ vcat
      [ "generalized"
      , nest 2 $ "t =" <+> escapeContext 1 (prettyTCM t') ]

    return (length sortedMetas, t')

metaCheckpoint :: MetaId -> TCM CheckpointId
metaCheckpoint m = do
  mv <- lookupMeta m
  enterClosure (miClosRange $ mvInfo mv) $ \ _ -> viewTC eCurrentCheckpoint

unpackSub :: ConHead -> [ArgInfo] -> Int -> Substitution
unpackSub con infos i = recSub
  where
    ar = length infos
    appl info v = Apply (Arg info v)
    -- recVal = con (var (i - 1)) .. (var 0) __IMPOSSIBLE__ .. __IMPOSSIBLE__
    recVal = Con con ConOSystem $ zipWith appl infos $ [var j | j <- [i - 1, i - 2..0]] ++ replicate (ar - i) __DUMMY_TERM__

    -- want: Γ Δᵢ ⊢ recSub i : Γ (r : R)
    -- have:
    -- Γ Δᵢ ⊢ recVal i :# σ : Θ (r : R),  if Γ Δᵢ ⊢ σ : Θ
    -- Γ Δᵢ ⊢ WkS i IdS : Γ
    recSub = recVal :# Wk i IdS

buildGeneralizeTel :: ConHead -> [(Arg String, Type)] -> Telescope
buildGeneralizeTel con xs = go 0 xs
  where
    infos = map (argInfo . fst) xs
    recSub i = unpackSub con infos i
    go _ [] = EmptyTel
    go i ((name, ty) : xs) = ExtendTel (dom ty') $ Abs (unArg name) $ go (i + 1) xs
      where ty' = applySubst (recSub i) ty
            dom = setArgInfo (argInfo name) . defaultDom

-- | Create a generalisable meta for a generalisable variable.
createGenValue :: QName -> TCM (QName, GeneralizedValue)
createGenValue x = do
  cp  <- viewTC eCurrentCheckpoint
  def <- instantiateDef =<< getConstInfo x
                   -- Only prefix of generalizable arguments (for now?)
  let nGen       = case defArgGeneralizable def of
                     NoGeneralizableArgs     -> 0
                     SomeGeneralizableArgs n -> n
      ty         = defType def
      TelV tel _ = telView' ty
      -- Generalizable variables are never explicit, so if they're given as
      -- explicit we default to hidden.
      hideExplicit arg | visible arg = hide arg
                       | otherwise   = arg
      argTel     = telFromList $ map hideExplicit $ take nGen $ telToList tel

  args <- newTelMeta argTel

  let metaType = piApply ty args
      name     = show (nameConcrete $ qnameName x)
  (m, term) <- newNamedValueMeta DontRunMetaOccursCheck name metaType

  -- Freeze the meta to prevent named generalizable metas to be instantiated.
  let fromJust' :: Lens' a (Maybe a)
      fromJust' f (Just x) = Just <$> f x
      fromJust' f Nothing  = {-'-} __IMPOSSIBLE__
  stMetaStore . key m . fromJust' . metaFrozen `setTCLens` Frozen

  -- Set up names of arg metas
  forM_ (zip3 [1..] (map unArg args) (telToList argTel)) $ \ case
    (i, MetaV m _, Dom{unDom = (x, _)}) -> do
      let suf "_" = show i
          suf ""  = show i
          suf x   = x
      setMetaNameSuggestion m (name ++ "." ++ suf x)
    _ -> return ()  -- eta expanded

  -- Update the ArgInfos for the named meta. The argument metas are
  -- created with the correct ArgInfo.
  setMetaArgInfo m $ hideExplicit (defArgInfo def)

  reportSDoc "tc.decl.gen" 50 $ vcat
    [ "created metas for generalized variable" <+> prettyTCM x
    , nest 2 $ "top  =" <+> prettyTCM term
    , nest 2 $ "args =" <+> prettyTCM args ]

  case term of
    MetaV{} -> return ()
    _       -> genericDocError =<< ("Cannot generalize over" <+> prettyTCM x <+> "of eta-expandable type") <?>
                                    prettyTCM metaType
  return (x, GeneralizedValue{ genvalCheckpoint = cp
                             , genvalTerm       = term
                             , genvalType       = metaType })

-- | Sort metas in dependency order.
sortMetas :: [MetaId] -> TCM [MetaId]
sortMetas metas = do
  metaGraph <- fmap concat $ forM metas $ \ m -> do
                  deps <- nub . filter (`elem` metas) . allMetas <$> (instantiateFull =<< getMetaType m)
                  return [ (m, m') | m' <- deps ]

  caseMaybe (Graph.topSort metas metaGraph)
            (typeError GeneralizeCyclicDependency)
            return

createGenRecordType :: Type -> [MetaId] -> TCM (QName, ConHead, [QName])
createGenRecordType genRecMeta@(El genRecSort _) sortedMetas = do
  current <- currentModule
  let freshQName s = qualify current <$> freshName_ (s :: String)
      mkFieldName  = freshQName . (generalizedFieldName ++) <=< getMetaNameSuggestion
  genRecFields <- mapM (defaultArg <.> mkFieldName) sortedMetas
  genRecName   <- freshQName "GeneralizeTel"
  genRecCon    <- freshQName "mkGeneralizeTel" <&> \ con -> ConHead
                  { conName      = con
                  , conInductive = Inductive
                  , conFields    = genRecFields }
  forM_ genRecFields $ \ fld -> do
    let field   = unArg fld     -- Filled in later
        fieldTy = El __DUMMY_SORT__ $ Pi (defaultDom __DUMMY_TYPE__) (Abs "_" __DUMMY_TYPE__)
    addConstant field $ defaultDefn (argInfo fld) field fieldTy $
      let proj = Projection { projProper   = Just genRecName
                            , projOrig     = field
                            , projFromType = defaultArg genRecName
                            , projIndex    = 1
                            , projLams     = ProjLams [defaultArg "gtel"] } in
      Function { funClauses      = []
               , funCompiled     = Nothing
               , funTreeless     = Nothing
               , funInv          = NotInjective
               , funMutual       = Nothing
               , funAbstr        = ConcreteDef
               , funDelayed      = NotDelayed
               , funProjection   = Just proj
               , funFlags        = Set.empty
               , funTerminates   = Just True
               , funExtLam       = Nothing
               , funWith         = Nothing
               , funCopatternLHS = False
               }
  addConstant (conName genRecCon) $ defaultDefn defaultArgInfo (conName genRecCon) __DUMMY_TYPE__ $ -- Filled in later
    Constructor { conPars   = 0
                , conArity  = length genRecFields
                , conSrcCon = genRecCon
                , conData   = genRecName
                , conAbstr  = ConcreteDef
                , conInd    = Inductive
                , conComp   = Nothing
                , conForced = []
                , conErased = []
                }
  addConstant genRecName $ defaultDefn defaultArgInfo genRecName (sort genRecSort) $
    Record { recPars         = 0
           , recClause       = Nothing
           , recConHead      = genRecCon
           , recNamedCon     = False
           , recFields       = genRecFields
           , recTel          = EmptyTel     -- Filled in later
           , recMutual       = Nothing
           , recEtaEquality' = Inferred YesEta
           , recInduction    = Nothing
           , recAbstr        = ConcreteDef
           , recComp         = Nothing }
  reportSDoc "tc.decl.gen" 40 $ vcat
    [ text "created genRec" <+> text (show genRecFields) ]
  -- Solve the genRecMeta
  args <- getContextArgs
  let genRecTy = El genRecSort $ Def genRecName $ map Apply args
  noConstraints $ equalType genRecTy genRecMeta
  return (genRecName, genRecCon, map unArg genRecFields)

fillInGenRecordDetails :: QName -> ConHead -> [QName] -> Type -> Telescope -> TCM ()
fillInGenRecordDetails name con fields recTy fieldTel = do
  cxtTel <- fmap hideAndRelParams <$> getContextTelescope
  let fullTel = cxtTel `abstract` fieldTel
  -- Field types
  let mkFieldTypes [] EmptyTel = []
      mkFieldTypes (fld : flds) (ExtendTel ty ftel) =
          abstract cxtTel (El s $ Pi (defaultDom recTy) (Abs "r" $ unDom ty)) :
          mkFieldTypes flds (absApp ftel proj)
        where
          s = PiSort (getSort recTy) (Abs "r" $ getSort ty)
          proj = Var 0 [Proj ProjSystem fld]
      mkFieldTypes _ _ = __IMPOSSIBLE__
  let fieldTypes = mkFieldTypes fields (raise 1 fieldTel)
  reportSDoc "tc.decl.gen" 40 $ text "Field types:" <+> inTopContext (nest 2 $ vcat $ map prettyTCM fieldTypes)
  zipWithM_ setType fields fieldTypes
  -- Constructor type
  let conType = fullTel `abstract` raise (size fieldTel) recTy
  reportSDoc "tc.decl.gen" 40 $ text "Final genRecCon type:" <+> inTopContext (prettyTCM conType)
  setType (conName con) conType
  -- Record telescope: Includes both parameters and fields.
  modifyGlobalDefinition name $ \ r ->
    r { theDef = (theDef r) { recTel = fullTel } }
  where
    setType q ty = modifyGlobalDefinition q $ \ d -> d { defType = ty }

