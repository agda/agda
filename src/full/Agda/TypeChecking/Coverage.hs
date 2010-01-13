{-# LANGUAGE CPP #-}

module Agda.TypeChecking.Coverage where

import Control.Monad
import Control.Monad.Error
import Control.Applicative
import Data.List
import qualified Data.Set as Set
import Data.Set (Set)

import Agda.Syntax.Position
import Agda.Syntax.Common
import Agda.Syntax.Internal
import Agda.Syntax.Internal.Pattern

import Agda.TypeChecking.Monad.Base
import Agda.TypeChecking.Monad.Trace
import Agda.TypeChecking.Monad.Signature
import Agda.TypeChecking.Monad.Options
import Agda.TypeChecking.Monad.Exception
import Agda.TypeChecking.Monad.Context

import Agda.TypeChecking.Rules.LHS.Unify
import Agda.TypeChecking.Rules.LHS.Instantiate
import Agda.TypeChecking.Rules.LHS

import Agda.TypeChecking.Coverage.Match

import Agda.TypeChecking.Pretty
import Agda.TypeChecking.Substitute
import Agda.TypeChecking.Reduce
import Agda.TypeChecking.Primitive (constructorForm)
import Agda.TypeChecking.Telescope

import Agda.Interaction.Options

import Agda.Utils.Permutation
import Agda.Utils.Size
import Agda.Utils.Tuple
import Agda.Utils.Monad

#include "../undefined.h"
import Agda.Utils.Impossible

data SplitClause = SClause
      { scTel   :: Telescope      -- ^ type of variables in scPats
      , scPerm  :: Permutation    -- ^ how to get from the variables in the patterns to the telescope
      , scPats  :: [Arg Pattern]
      , scSubst :: [Term]         -- ^ substitution from scTel to old context
      }

type Covering = [SplitClause]

typeOfVar :: Telescope -> Nat -> Type
typeOfVar tel n
  | n >= len  = __IMPOSSIBLE__
  | otherwise = snd . unArg $ ts !! fromIntegral n
  where
    len = genericLength ts
    ts  = reverse $ telToList tel

-- | Top-level function for checking pattern coverage.
checkCoverage :: QName -> TCM ()
checkCoverage f = do
  d <- getConstInfo f
  TelV gamma _ <- telView $ defType d
  let defn = theDef d
  case defn of
    Function{ funClauses = cs@(_:_) } -> do
      let n            = genericLength $ clausePats $ head cs
          gamma'       = telFromList $ genericTake n $ telToList gamma
          xs           = map (fmap $ const $ VarP "_") $ telToList gamma'
      reportSDoc "tc.cover.top" 10 $ vcat
        [ text "Coverage checking"
        , nest 2 $ vcat $ map (text . show . clausePats) cs
        ]
      (used, pss) <- cover cs $ SClause gamma' (idP n) xs (idSub gamma')
      whenM (optCompletenessCheck <$> commandLineOptions) $
        case pss of
          []  -> return ()
          _   ->
            setCurrentRange (getRange cs) $
              typeError $ CoverageFailure f pss
      whenM (optUnreachableCheck <$> commandLineOptions) $
        case Set.toList $ Set.difference (Set.fromList [0..genericLength cs - 1]) used of
          []  -> return ()
          is  -> do
            let unreached = map ((cs !!) . fromIntegral) is
            setCurrentRange (getRange unreached) $
              typeError $ UnreachableClauses f (map clausePats unreached)
    _             -> __IMPOSSIBLE__

-- | Check that the list of clauses covers the given split clause.
--   Returns the missing cases.
cover :: MonadTCM tcm => [Clause] -> SplitClause -> tcm (Set Nat, [[Arg Pattern]])
cover cs (SClause tel perm ps _) = do
  reportSDoc "tc.cover.cover" 10 $ vcat
    [ text "checking coverage of pattern:"
    , nest 2 $ text "tel  =" <+> prettyTCM tel
    , nest 2 $ text "perm =" <+> text (show perm)
    , nest 2 $ text "ps   =" <+> text (show ps)
    ]
  case match cs ps perm of
    Yes i          -> do
      reportSLn "tc.cover.cover" 10 $ "pattern covered by clause " ++ show i
      -- Check if any earlier clauses could match with appropriate literals
      let is = [ j | (j, c) <- zip [0..] (genericTake i cs), matchLits c ps perm ]
      reportSLn "tc.cover.cover"  10 $ "literal matches: " ++ show is
      return (Set.fromList (i : is), [])
    No             -> return (Set.empty, [ps])
    Block Nothing  -> fail $ "blocked by dot pattern"
    Block (Just x) -> do
      r <- split tel perm ps x
      case r of
        Left err  -> case err of
          CantSplit c _ _ _ _ -> typeError $ CoverageCantSplitOn c
          NotADatatype a      -> typeError $ CoverageCantSplitType a
          GenericSplitError s -> fail $ "failed to split: " ++ s
        Right scs -> (Set.unions -*- concat) . unzip <$> mapM (cover cs) scs

-- | Check that a type is a datatype
isDatatype :: MonadTCM tcm => Type -> tcm (Maybe (QName, [Arg Term], [Arg Term], [QName]))
isDatatype t = do
  t <- normalise t
  case unEl t of
    Def d args -> do
      def <- theDef <$> getConstInfo d
      case def of
        Datatype{dataPars = np, dataCons = cs} -> do
          let (ps, is) = genericSplitAt np args
          return $ Just (d, ps, is, cs)
        Record{recPars = np, recCon = Just c} ->
          return $ Just (d, args, [], [c])
        _ -> return Nothing
    _ -> return Nothing

data SplitError = NotADatatype Type
                | CantSplit QName Telescope Args Args [Term]
                | GenericSplitError String
  deriving (Show)

instance Error SplitError where
  noMsg  = strMsg ""
  strMsg = GenericSplitError

type CoverM = ExceptionT SplitError TCM

-- | @dtype == d pars ixs@
computeNeighbourhood :: Telescope -> Telescope -> Permutation -> QName -> Args -> Args -> Nat -> OneHolePatterns -> QName -> CoverM [SplitClause]
computeNeighbourhood delta1 delta2 perm d pars ixs hix hps con = do

  -- Get the type of the datatype
  dtype <- normalise =<< (`piApply` pars) . defType <$> getConstInfo d

  -- Get the real constructor name
  Con con [] <- constructorForm =<< normalise (Con con [])

  -- Get the type of the constructor
  ctype <- defType <$> getConstInfo con

  -- Lookup the type of the constructor at the given parameters
  TelV gamma (El _ (Def _ cixs)) <- telView (ctype `piApply` pars)

  debugInit con ctype pars ixs cixs delta1 delta2 gamma hps hix

  -- All variables are flexible
  let flex = [0..size delta1 + size gamma - 1]

  -- Unify constructor target and given type (in Δ₁Γ)
  let conIxs   = drop (size pars) cixs
      givenIxs = raise (size gamma) ixs

  r <- addCtxTel (delta1 `abstract` gamma) $
       unifyIndices flex (raise (size gamma) dtype) conIxs givenIxs

  case r of
    NoUnify _ _ _ -> do
      debugNoUnify
      return []
    DontKnow _    -> do
      debugCantSplit
      throwException $ CantSplit con (delta1 `abstract` gamma) conIxs givenIxs
                                 [ Var i [] | i <- flex ]
    Unifies sub   -> do
      debugSubst "sub" sub

      -- Substitute the constructor for x in Δ₂: Δ₂' = Δ₂[conv/x]
      let conv    = Con con  $ teleArgs gamma   -- Θ Γ ⊢ conv (for any Θ)
          delta2' = subst conv $ raiseFrom 1 (size gamma) delta2
      debugTel "delta2'" delta2'

      -- Compute a substitution ρ : Δ₁ΓΔ₂' → Δ₁(x:D)Δ₂
      let rho = [ Var i [] | i <- [0..size delta2' - 1] ]
             ++ [ raise (size delta2') conv ]
             ++ [ Var i [] | i <- [size delta2' + size gamma ..] ]

      -- Plug the hole with the constructor and apply ρ
      let conp = ConP con $ map (fmap VarP) $ teleArgNames gamma
          ps   = plugHole conp hps
          ps'  = substs rho ps      -- Δ₁ΓΔ₂' ⊢ ps'
      debugPlugged ps ps'

      -- Δ₁Γ ⊢ sub, we need something in Δ₁ΓΔ₂'
      -- Also needs to be padded with Nothing's to have the right length.
      let pad n xs x = xs ++ replicate (max 0 $ n - size xs) x
          sub'       = replicate (size delta2') Nothing ++
                       pad (size delta1 + size gamma) (raise (size delta2') sub) Nothing
      debugSubst "sub'" sub'

      -- Θ = Δ₁ΓΔ₂'
      let theta = delta1 `abstract` gamma `abstract` delta2'
      debugTel "theta" theta

      -- Apply the unifying substitution to Θ
      -- We get ρ' : Θ' -> Θ
      --        π  : Θ' -> Θ
      (theta', iperm, rho', _) <- instantiateTel sub' theta
      debugTel "theta'" theta'
      debugShow "iperm" iperm

      -- Compute final permutation
      let perm' = expandP hix (size gamma) perm -- perm' : Θ -> Δ₁(x : D)Δ₂
          rperm = iperm `composeP` perm'
      debugShow "perm'" perm'
      debugShow "rperm" rperm

      -- Compute the final patterns
      let ps'' = instantiatePattern sub' perm' ps'
          rps  = substs rho' ps''

      -- Compute the final substitution
      let rsub  = substs rho' rho

      debugFinal theta' rperm rps

      return [SClause theta' rperm rps rsub]

  where
    debugInit con ctype pars ixs cixs delta1 delta2 gamma hps hix =
      reportSDoc "tc.cover.split.con" 20 $ vcat
        [ text "computeNeighbourhood"
        , nest 2 $ vcat
          [ text "con    =" <+> prettyTCM con
          , text "ctype  =" <+> prettyTCM ctype
          , text "hps    =" <+> text (show hps)
          , text "pars   =" <+> prettyList (map prettyTCM pars)
          , text "ixs    =" <+> addCtxTel (delta1 `abstract` gamma) (prettyList (map prettyTCM ixs))
          , text "cixs   =" <+> prettyList (map prettyTCM cixs)
          , text "delta1 =" <+> prettyTCM delta1
          , text "delta2 =" <+> prettyTCM delta2
          , text "gamma  =" <+> prettyTCM gamma
          , text "hix    =" <+> text (show hix)
          ]
        ]

    debugNoUnify =
      reportSLn "tc.cover.split.con" 20 "  Constructor impossible!"

    debugCantSplit =
      reportSLn "tc.cover.split.con" 20 "  Bad split!"

    debugSubst s sub =
      reportSDoc "tc.cover.split.con" 20 $ nest 2 $ vcat
        [ text (s ++ " =") <+> brackets (fsep $ punctuate comma $ map (maybe (text "_") prettyTCM) sub)
        ]

    debugTel s tel =
      reportSDoc "tc.cover.split.con" 20 $ nest 2 $ vcat
        [ text (s ++ " =") <+> prettyTCM tel
        ]

    debugShow s x =
      reportSDoc "tc.cover.split.con" 20 $ nest 2 $ vcat
        [ text (s ++ " =") <+> text (show x)
        ]

    debugPlugged ps ps' =
      reportSDoc "tc.cover.split.con" 20 $ nest 2 $ vcat
        [ text "ps     =" <+> text (show ps)
        , text "ps'    =" <+> text (show ps')
        ]

    debugFinal tel perm ps =
      reportSDoc "tc.cover.split.con" 20 $ nest 2 $ vcat
        [ text "rtel   =" <+> prettyTCM tel
        , text "rperm  =" <+> text (show perm)
        , text "rps    =" <+> text (show ps)
        ]

-- | split Δ x ps. Δ ⊢ ps, x ∈ Δ (deBruijn index)
splitClause :: Clause -> Nat -> TCM (Either SplitError Covering)
splitClause c x = split (clauseTel c) (clausePerm c) (clausePats c) x

splitClauseWithAbs :: Clause -> Nat -> TCM (Either SplitError (Either SplitClause Covering))
splitClauseWithAbs c x = split' (clauseTel c) (clausePerm c) (clausePats c) x

split :: MonadTCM tcm => Telescope -> Permutation -> [Arg Pattern] -> Nat ->
         tcm (Either SplitError Covering)
split tel perm ps x = do
  r <- split' tel perm ps x
  return $ case r of
    Left err        -> Left err
    Right (Left _)  -> Right []
    Right (Right c) -> Right c

split' :: MonadTCM tcm => Telescope -> Permutation -> [Arg Pattern] -> Nat ->
         tcm (Either SplitError (Either SplitClause Covering))
split' tel perm ps x = liftTCM $ runExceptionT $ do

  debugInit tel perm x ps

  -- Split the telescope at the variable
  (delta1, delta2) <- do
    let (tel1, _ : tel2) = genericSplitAt (size tel - x - 1) $ telToList tel
    return (telFromList tel1, telFromList tel2)

  -- Get the type of the variable
  t <- normalise $ typeOfVar tel x  -- Δ₁ ⊢ t

  -- Compute the one hole context of the patterns at the variable
  (hps, hix) <- do
    let holes = reverse $ permute perm $ zip [0..] $ allHolesWithContents ps
    unless (length holes == length (telToList tel)) $
      fail "split: bad holes or tel"

    -- There is always a variable at the given hole.
    let (hix, (VarP s, hps)) = holes !! fromIntegral x
    debugHoleAndType s hps t

    return (hps, hix)

  -- Check that t is a datatype
  (d, pars, ixs, cons) <- do
    dt <- isDatatype t
    case dt of
      Nothing -> throwException $ NotADatatype t
      Just d  -> return d

  -- Compute the neighbourhoods for the constructors
  ns <- concat <$> mapM (computeNeighbourhood delta1 delta2 perm d pars ixs hix hps) cons
  case ns of
    []  -> do
      let absurd = VarP "()"
      return $ Left $ SClause
               { scTel  = telFromList $ telToList delta1 ++
                                        [Arg NotHidden ("()", t)] ++
                                        telToList delta2
               , scPerm = perm
               , scPats = plugHole absurd hps
               , scSubst = [] -- not used anyway
               }

    _   -> return $ Right ns

  where

    -- Debug printing
    debugInit tel perm x ps =
      reportSDoc "tc.cover.top" 10 $ vcat
        [ text "split"
        , nest 2 $ vcat
          [ text "tel  =" <+> prettyTCM tel
          , text "perm =" <+> text (show perm)
          , text "x    =" <+> text (show x)
          , text "ps   =" <+> text (show ps)
          ]
        ]

    debugHoleAndType s hps t =
      reportSDoc "tc.cover.top" 10 $ nest 2 $ vcat $
        [ text "p   =" <+> text s
        , text "hps =" <+> text (show hps)
        , text "t   =" <+> prettyTCM t
        ]
