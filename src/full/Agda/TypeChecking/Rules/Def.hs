{-# LANGUAGE CPP #-}

module Agda.TypeChecking.Rules.Def where

import Prelude hiding (mapM)
import Control.Arrow ((***), (&&&))
import Control.Applicative
import Control.Monad.State hiding (mapM)
import Control.Monad.Reader hiding (mapM)
import Control.Monad.Error hiding (mapM)
import Control.Monad hiding (mapM)

import Data.Function
import Data.List hiding (sort)
import Data.Traversable
import Data.Set (Set)
import qualified Data.Set as Set

import Agda.Syntax.Common
import Agda.Syntax.Position
import qualified Agda.Syntax.Abstract as A
import Agda.Syntax.Internal
import qualified Agda.Syntax.Info as Info
import qualified Agda.Syntax.Abstract.Pretty as A
import Agda.Syntax.Fixity
import Agda.Syntax.Translation.InternalToAbstract
import Agda.Syntax.Info
import Agda.Syntax.Scope.Base (emptyScopeInfo)
import Agda.TypeChecking.Monad
import Agda.TypeChecking.Monad.Builtin (primRefl, primEquality)
import Agda.TypeChecking.Reduce
import Agda.TypeChecking.Pretty
import Agda.TypeChecking.Substitute
import Agda.TypeChecking.Free
import Agda.TypeChecking.Constraints
import Agda.TypeChecking.Conversion
import Agda.TypeChecking.Empty
import Agda.TypeChecking.MetaVars
import Agda.TypeChecking.Rebind
import Agda.TypeChecking.Primitive hiding (Nat)
import Agda.TypeChecking.With
import Agda.TypeChecking.Telescope
import Agda.TypeChecking.Coverage
import Agda.TypeChecking.Injectivity
import Agda.TypeChecking.Polarity
import Agda.TypeChecking.Irrelevance
import Agda.TypeChecking.Implicit
import Agda.TypeChecking.SizedTypes
import Agda.TypeChecking.CompiledClause (CompiledClauses(..))
import Agda.TypeChecking.CompiledClause.Compile

import Agda.TypeChecking.Rules.Term                ( checkExpr, inferExpr, inferExprForWith, inferOrCheck, checkTelescope_, isType_ )
import Agda.TypeChecking.Rules.LHS                 ( checkLeftHandSide )
import Agda.TypeChecking.Rules.LHS.Implicit        ( insertImplicitPatterns )
import {-# SOURCE #-} Agda.TypeChecking.Rules.Decl ( checkDecls )
import Agda.TypeChecking.Rules.Data                ( isCoinductive )

import Agda.Interaction.Options

import Agda.Utils.Tuple
import Agda.Utils.Size
import Agda.Utils.Function
import Agda.Utils.List
import Agda.Utils.Permutation
import Agda.Utils.Monad

#include "../../undefined.h"
import Agda.Utils.Impossible

---------------------------------------------------------------------------
-- * Definitions by pattern matching
---------------------------------------------------------------------------

checkFunDef :: Delayed -> Info.DefInfo -> QName -> [A.Clause] -> TCM ()
checkFunDef delayed i name cs = do
        -- Get the type and relevance of the function
        t    <- typeOfConst name
        rel  <- relOfConst name
        case trivialClause cs of
          -- if we have just one clause without pattern matching and
          -- without a type signature, then infer, to allow
          -- "aliases" for things starting with hidden abstractions
          Just e | isMeta (ignoreSharing $ unEl t) ->
            traceCall (CheckFunDef (getRange i) (qnameName name) cs) $
              checkAlias t rel delayed i name e
          _ -> checkFunDef' t rel delayed i name cs
  where
    isMeta MetaV{} = True
    isMeta _       = False
    trivialClause [A.Clause (A.LHS i (A.LHSHead f []) []) (A.RHS e) []] = Just e
    trivialClause _ = Nothing

-- | Check a trivial definition of the form @f = e@
checkAlias :: Type -> Relevance -> Delayed -> Info.DefInfo -> QName -> A.Expr -> TCM ()
checkAlias t' rel delayed i name e = do
  reportSDoc "tc.def.alias" 10 $ text "checkAlias" <+> vcat
    [ text (show name) <+> colon  <+> prettyTCM t'
    , text (show name) <+> equals <+> prettyTCM e
    ]
  -- Infer the type of the rhs
  (v, t) <- applyRelevanceToContext rel $ inferOrCheck e (Just t')
  -- v <- coerce v t t'
  reportSDoc "tc.def.alias" 20 $ text "checkAlias: finished checking"

  solveSizeConstraints

  v <- instantiateFull v  -- if we omit this, we loop (stdlib: Relation.Binary.Sum)
    -- or the termination checker might stumble over levels in sorts
    -- that cannot be converted to expressions without the level built-ins
    -- (test/succeed/Issue655.agda)

  -- Add the definition
  addConstant name $ Defn rel name t [] [] (defaultDisplayForm name) 0 noCompiledRep
                   $ Function
                      { funClauses        = [Clause (getRange i) EmptyTel (idP 0) [] $ Body v] -- trivial clause @name = v@
                      , funCompiled       = Done [] v
                      , funDelayed        = delayed
                      , funInv            = NotInjective
                      , funAbstr          = Info.defAbstract i
{-
                      , funPolarity       = []
                      , funArgOccurrences = []
-}
                      , funMutual         = []
                      , funProjection     = Nothing
                      , funStatic         = False
                      , funCopy           = False
                      }
  reportSDoc "tc.def.alias" 20 $ text "checkAlias: leaving"


-- | Type check a definition by pattern matching. The third argument
-- specifies whether the clauses are delayed or not.
checkFunDef' :: Type -> Relevance -> Delayed -> Info.DefInfo -> QName -> [A.Clause] -> TCM ()
checkFunDef' t rel delayed i name cs =

    traceCall (CheckFunDef (getRange i) (qnameName name) cs) $ do   -- TODO!! (qnameName)
        reportSDoc "tc.def.fun" 10 $
          sep [ text "checking body of" <+> prettyTCM name
              , nest 2 $ text ":" <+> prettyTCM t
              , nest 2 $ text "full type:" <+> (prettyTCM . defType =<< getConstInfo name)
              ]

        -- Ensure that all clauses have the same number of trailing hidden patterns
        -- This is necessary since trailing implicits are no longer eagerly inserted.
        cs <- trailingImplicits t cs

        -- Check the clauses
        let check c = do
              c <- applyRelevanceToContext rel $ checkClause t c
              solveSizeConstraints
              return c
        cs <- traceCall NoHighlighting $  -- To avoid flicker.
                mapM check cs

        -- Check that all clauses have the same number of arguments
        unless (allEqual $ map npats cs) $ typeError DifferentArities

        reportSDoc "tc.cc" 15 $ do
          sep [ text "clauses before rebindClause"
              , nest 2 $ prettyTCM (map (NamedClause name) cs)
              ]

        -- Annotate the clauses with which arguments are actually used.
        cs <- instantiateFull =<< mapM rebindClause cs
        -- Andreas, 2010-11-12
        -- rebindClause is the identity, and instantiateFull eta-contracts
        -- removing this eta-contraction fixes issue 361
        -- however, Data.Star.Decoration.gmapAll no longer type-checks
        -- possibly due to missing eta-contraction!?

        -- Check if the function is injective
        inv <- checkInjectivity name cs

        reportSDoc "tc.cc" 15 $ do
          sep [ text "clauses before compilation"
              , nest 2 $ prettyTCM (map (NamedClause name) cs)
              ]

        -- Coverage check and compile the clauses
        cc <- compileClauses (Just (name, t)) cs

        reportSDoc "tc.cc" 10 $ do
          sep [ text "compiled clauses of" <+> prettyTCM name
              , nest 2 $ text (show cc)
              ]

        -- Add the definition
        addConstant name $ Defn rel name t [] [] (defaultDisplayForm name) 0 noCompiledRep
                         $ Function
                            { funClauses        = cs
                            , funCompiled       = cc
                            , funDelayed        = delayed
                            , funInv            = inv
                            , funAbstr          = Info.defAbstract i
{-
                            , funPolarity       = []
                            , funArgOccurrences = []
-}
                            , funMutual         = []
                            , funProjection     = Nothing
                            , funStatic         = False
                            , funCopy           = False
                            }

        -- Andreas 2012-02-13: postpone polarity computation until after positivity check
        -- computePolarity name

        reportSDoc "tc.def.fun" 10 $ do
          sep [ text "added " <+> prettyTCM name <+> text ":"
              , nest 2 $ prettyTCM . defType =<< getConstInfo name
              ]
    where
        npats = size . clausePats

{- | Ensure that all clauses have the same number of trailing implicits.
Example:

@
  test : Bool → {A B : Set} → Set
  test true  {A}     = A
  test false {B = B} = B
@

@trailingImplicits@ patches these clauses to

@
  test : Bool → {A B : Set} → Set
  test true  {A} {_}     = A
  test false {_} {B = B} = B
@

such that the arity of the clauses of @test@ is uniform.
-}
trailingImplicits :: Type -> [A.Clause] -> TCM [A.Clause]
trailingImplicits t []       = __IMPOSSIBLE__
trailingImplicits t cs@(c:_) = do
  pps@((ps,ips):_) <- mapM splitTrailingImplicits cs
  -- compute the trailing implicits from type t
  TelV tel t0 <- telView t
  let -- number of non-hidden patterns
      nh  = genericLength $ filter ((NotHidden ==) . argHiding) ps
      -- drop nh non-hidden domains from t
      l   = dropNonHidden nh $ telToList tel
      -- take the hidden domains immediately after the dropped stuff
      is   = takeWhile ((NotHidden /=) . domHiding) l
      itel = telFromList is
      -- get the trailing implicit patterns
      ipss = map snd pps
  -- complete the implicit pattern lists
  ipss <- mapM (\ ps -> insertImplicitPatterns DontExpandLast ps itel) ipss
  let longest = head $ sortBy (compare `on` ((0-) . length)) ipss
      pps' = zip (map fst pps) ipss
  return $ zipWith (patchUpTrailingImplicits longest) pps' cs

-- | @dropNonHidden n tel@ drops @n@ non-hidden domains from @tel@,
--   including all hidden domains that come before the @n@th non-hidden one.
dropNonHidden :: Nat -> [Dom (String, Type)] -> [Dom (String, Type)]
dropNonHidden 0 l = l
dropNonHidden n l = case dropWhile ((NotHidden /=) . domHiding) l of
  []    -> [] -- or raise a type checking error "too many arguments in lhs"
  (_:l) -> dropNonHidden (n-1) l

-- | @splitTrailingImplicits c@ returns the patterns of clause @c@
--   as pair @(ps, ips)@ where @ips@ are the trailing implicit patterns
--   and @ps@ is the rest.
splitTrailingImplicits :: A.Clause -> TCM (A.Patterns, A.Patterns)
splitTrailingImplicits (A.Clause (A.LHS _ A.LHSProj{} []) _ _) =
  typeError $ NotImplemented "type checking definitions by copatterns"
splitTrailingImplicits (A.Clause (A.LHS _ _ ps@(_ : _)) _ _) =
  typeError $ UnexpectedWithPatterns ps
splitTrailingImplicits (A.Clause (A.LHS _ (A.LHSHead _ aps) []) _ _) = do
  let (ips, ps) = span ((Hidden==) . argHiding) $ reverse aps
  return (reverse ps, reverse ips)

{- UNUSED
-- | Compute the difference between two list of hidden patterns.
--   The first pattern list must be longer.
--   Both pattern lists must be complete, i.e., not skip any hidden patterns.
patternDiff :: A.Patterns -> A.Patterns -> A.Patterns
patternDiff ps1 ps2 = drop (length ps2) ps1
-}

-- | @patchUpTrailingImplicits should (ps, is) c@ takes a clause @c@ whose
--   patterns are split into @(ps, is)@ where @is@ are the trailing
--   implicit patterns and @ps@ the rest.  @is@ has already been patched
--   with omitted implicit patterns (which can occur if named implicit patterns
--   are there originally).  @should@ is an extension of @is@.
--   The returned clause contains an extension of @is@ by new wildcards
--   to match @should@.
patchUpTrailingImplicits :: A.Patterns -> (A.Patterns, A.Patterns) -> A.Clause -> A.Clause
patchUpTrailingImplicits should (ps, is) c | length is >= length should = c
patchUpTrailingImplicits should (ps, is) (A.Clause (A.LHS i (A.LHSHead x aps) []) rhs0 wh) =
  let imp  = Arg Hidden Relevant $ Named Nothing $ A.ImplicitP $
               Info.PatRange noRange
      imps = replicate (length should - length is) imp
  in  A.Clause (A.LHS i (A.LHSHead x (ps ++ is ++ imps)) []) rhs0 wh
patchUpTrailingImplicits _ _ _ = __IMPOSSIBLE__

{- OLD
-- | Ensure that all clauses have the same number of trailing implicits.
trailingImplicits :: [A.Clause] -> TCM [A.Clause]
trailingImplicits [] = __IMPOSSIBLE__
trailingImplicits cs = do
  ns <- mapM numberOfTrailingImplicits cs
  let n = maximum ns
  return $ zipWith (patchUpTrailingImplicits n) ns cs

numberOfTrailingImplicits :: A.Clause -> TCM Int
numberOfTrailingImplicits (A.Clause (A.LHS _ A.LHSProj{} []) _ _) =
  typeError $ NotImplemented "type checking definitions by copatterns"
numberOfTrailingImplicits (A.Clause (A.LHS _ _ ps@(_ : _)) _ _) =
  typeError $ UnexpectedWithPatterns ps
numberOfTrailingImplicits (A.Clause (A.LHS _ (A.LHSHead _ aps) []) _ _) =
  return $ length $ takeWhile ((Hidden==) . argHiding) $ reverse aps

patchUpTrailingImplicits :: Int -> Int -> A.Clause -> A.Clause
patchUpTrailingImplicits should is c | is >= should = c
patchUpTrailingImplicits should is (A.Clause (A.LHS i (A.LHSHead x aps) []) rhs0 wh) =
  let imp  = Arg Hidden Relevant $ Named Nothing $ A.ImplicitP $
               Info.PatRange noRange
      imps = replicate (should - is) imp
  in  A.Clause (A.LHS i (A.LHSHead x (aps ++ imps)) []) rhs0 wh
patchUpTrailingImplicits _ _ _ = __IMPOSSIBLE__
-}

-- | Insert some patterns in the in with-clauses LHS of the given RHS
insertPatterns :: [A.Pattern] -> A.RHS -> A.RHS
insertPatterns pats (A.WithRHS aux es cs) = A.WithRHS aux es (map insertToClause cs)
    where insertToClause (A.Clause (A.LHS i lhscore ps) rhs ds)
--              = A.Clause (A.LHS i x (aps ++ map (Arg NotHidden . unnamed) pats) (ps)) (insertPatterns pats rhs) ds
              = A.Clause (A.LHS i lhscore (pats ++ ps)) (insertPatterns pats rhs) ds
insertPatterns pats (A.RewriteRHS qs eqs rhs wh) = A.RewriteRHS qs eqs (insertPatterns pats rhs) wh
insertPatterns pats rhs = rhs


data WithFunctionProblem
      = NoWithFunction
      | WithFunction QName          -- parent function name
                     QName          -- with function name
                     Telescope      -- arguments to parent function
                     Telescope      -- arguments to the with function before the with expressions
                     Telescope      -- arguments to the with function after the with expressions
                     [Term]         -- with expressions
                     [Type]         -- types of the with expressions
                     Type           -- type of the right hand side
                     [Arg Pattern]  -- parent patterns
                     Permutation    -- permutation reordering the variables in the parent pattern
                     Permutation    -- final permutation (including permutation for the parent clause)
                     [A.Clause]     -- the given clauses for the with function

-- | Type check a function clause.
checkClause :: Type -> A.Clause -> TCM Clause
checkClause t c@(A.Clause (A.LHS i (A.LHSProj{}) []) rhs0 wh) =
  typeError $ NotImplemented "type checking definitions by copatterns"
checkClause t c@(A.Clause (A.LHS i (A.LHSHead x aps) []) rhs0 wh) =
    traceCall (CheckClause t c) $
    checkLeftHandSide (CheckPatternShadowing c) aps t $ \gamma delta sub xs ps t' perm -> do
      let mkBody v = foldr (\x t -> Bind $ Abs x t) (Body $ applySubst sub v) xs
      -- introduce trailing implicits for checking the where decls
      TelV htel t0 <- telViewUpTo' (-1) ((Hidden==) . domHiding) t'
      let n = size htel
      (body, with) <- addCtxTel htel $ checkWhere (size delta + n) wh $ escapeContext (size htel) $ let
          -- for the body, we remove the implicits again
          handleRHS rhs =
              case rhs of
                A.RHS e
                  | any (containsAbsurdPattern . namedThing . unArg) aps ->
                    typeError $ AbsurdPatternRequiresNoRHS aps
                  | otherwise -> do
                    v <- checkExpr e t'
                    return (mkBody v, NoWithFunction)
                A.AbsurdRHS
                  | any (containsAbsurdPattern . namedThing . unArg) aps
                              -> return (NoBody, NoWithFunction)
                  | otherwise -> typeError $ NoRHSRequiresAbsurdPattern aps
                A.RewriteRHS [] (_:_) _ _ -> __IMPOSSIBLE__
                A.RewriteRHS (_:_) [] _ _ -> __IMPOSSIBLE__
                A.RewriteRHS [] [] rhs [] -> handleRHS rhs
                A.RewriteRHS [] [] _ (_:_) -> __IMPOSSIBLE__
                A.RewriteRHS (qname:names) (eq:eqs) rhs wh -> do
                     (proof,t) <- inferExpr eq
                     t' <- reduce =<< instantiateFull t
                     equality <- primEquality >>= \eq ->
                      let lamV (Lam h b)  = ((h:) *** id) $ lamV (unAbs b)
                          lamV (Shared p) = lamV (derefPtr p)
                          lamV v          = ([], v) in
                      return $ case lamV eq of
                        ([Hidden, Hidden], Def equality _) -> equality
                        ([Hidden],         Def equality _) -> equality
                        ([],               Def equality _) -> equality
                        _                                  -> __IMPOSSIBLE__
                     reflCon <- primRefl >>= \refl -> return $ case ignoreSharing refl of
                         Con reflCon [] -> reflCon
                         _              -> __IMPOSSIBLE__
                     (rewriteType,rewriteFrom,rewriteTo) <- case ignoreSharing $ unEl t' of
                         Def equality' [_level, Arg Hidden Relevant rewriteType,
                                        Arg NotHidden Relevant rewriteFrom, Arg NotHidden Relevant rewriteTo]
                            | equality' == equality ->
                              return (rewriteType, rewriteFrom, rewriteTo)
                         _ -> do
                          err <- text "Cannot rewrite by equation of type" <+> prettyTCM t'
                          typeError $ GenericError $ show err

                     let info = PatRange noRange
                         metaInfo = Info.emptyMetaInfo
                         underscore = A.Underscore metaInfo

                     [rewriteFromExpr,rewriteToExpr,rewriteTypeExpr, proofExpr] <-
                      disableDisplayForms $ withShowAllArguments $ reify
                        [rewriteFrom,   rewriteTo,    rewriteType    , proof]
                     let (inner, outer) -- the where clauses should go on the inner-most with
                           | null eqs  = ([], wh)
                           | otherwise = (wh, [])
                         newRhs = A.WithRHS qname [rewriteFromExpr, proofExpr]
                                  [A.Clause (A.LHS i (A.LHSHead x aps) pats)
                                    (A.RewriteRHS names eqs (insertPatterns pats rhs) inner)
                                    outer]
                         pats = [A.DotP info underscore, -- rewriteToExpr,
                                 A.ConP info (AmbQ [reflCon]) []]
                     reportSDoc "tc.rewrite.top" 25 $ vcat
                                         [ text "from = " <+> prettyTCM rewriteFromExpr,
                                           text "to = " <+> prettyTCM rewriteToExpr,
                                           text "typ = " <+> prettyTCM rewriteType,
                                           text "proof = " <+> prettyTCM proofExpr,
                                           text "equ = " <+> prettyTCM t' ]
                     handleRHS newRhs

                A.WithRHS aux es cs -> do
                  reportSDoc "tc.with.top" 5 $
                    text "TC.Rules.Def.checkclause reached A.WithRHS"
                  reportSDoc "tc.with.top" 30 $
                    prettyA c
                  -- Infer the types of the with expressions
                  vas <- mapM inferExprForWith es
                  (vs0, as) <- instantiateFull (unzip vas)
                  (vs, as)  <- normalise (vs0, as)

                  -- Invent a clever name for the with function
                  m <- currentModule
                  reportSDoc "tc.with.top" 20 $ text "with function module:" <+> prettyList (map prettyTCM $ mnameToList m)

                  -- Split the telescope into the part needed to type the with arguments
                  -- and all the other stuff
                  let fv = allVars $ freeVars (vs, as)
                      SplitTel delta1 delta2 perm' = splitTelescope fv delta
                      finalPerm = composeP perm' perm

                  -- Andreas, 2012-09-17: for printing delta,
                  -- we should remove it from the context first
                  reportSDoc "tc.with.top" 25 $ escapeContext (size delta) $ vcat
                    [ text "delta  =" <+> prettyTCM delta
                    , text "delta1 =" <+> prettyTCM delta1
                    , text "delta2 =" <+> addCtxTel delta1 (prettyTCM delta2)
                    ]
                  reportSDoc "tc.with.top" 25 $ vcat
                    [ text "vs     =" <+> prettyTCM vs
                    , text "as     =" <+> prettyTCM as
                    , text "perm'  =" <+> text (show perm')
                    , text "perm   =" <+> text (show perm)
                    , text "fPerm  =" <+> text (show finalPerm)
                    ]

                  -- Create the body of the original function
{- OLD
                  ctx <- getContextTelescope
                  let n    = size ctx
                      m    = size delta
                      -- All the context variables
                      us   = [ Arg h r (var i) | (i, Arg h r _) <- zip [n - 1,n - 2..0] $ telToList ctx ]
-}
                  -- All the context variables
                  us <- getContextArgs
                  let n    = size us
                      m    = size delta
                      -- First the variables bound outside this definition
                      (us0, us1') = genericSplitAt (n - m) us
                      -- Then permute the rest and grab those needed to for the with arguments
                      (us1, us2)  = genericSplitAt (size delta1) $ permute perm' us1'
                      -- Now stuff the with arguments in between and finish with the remaining variables
                      v    = Def aux $ us0 ++ us1 ++ (map defaultArg vs0) ++ us2

                  -- We need Δ₁Δ₂ ⊢ t'
                  t' <- return $ renameP (reverseP perm') t'
                  -- and Δ₁ ⊢ vs : as
                  (vs, as) <- do
                    let -- We know that as does not depend on Δ₂
                        rho = parallelS (replicate (size delta2) __IMPOSSIBLE__)
                    return $ applySubst rho $ renameP (reverseP perm') (vs, as)

                  reportSDoc "tc.with.top" 20 $ vcat
                    [ text "    with arguments" <+> do escapeContext (size delta2) $ prettyList (map prettyTCM vs)
                    , text "             types" <+> do escapeContext (size delta2) $ prettyList (map prettyTCM as)
                    , text "with function call" <+> prettyTCM v
                    , text "           context" <+> (prettyTCM =<< getContextTelescope)
                    , text "             delta" <+> do escapeContext (size delta) $ prettyTCM delta
                    , text "                fv" <+> text (show fv)
                    , text "              body" <+> (addCtxTel delta $ prettyTCM $ mkBody v)
                    ]

                  return (mkBody v, WithFunction x aux gamma delta1 delta2 vs as t' ps perm' finalPerm cs)
          in handleRHS rhs0
      escapeContext (size delta) $ checkWithFunction with

      reportSDoc "tc.lhs.top" 10 $ escapeContext (size delta) $ vcat
        [ text "Clause before translation:"
        , nest 2 $ vcat
          [ text "delta =" <+> prettyTCM delta
          , text "perm  =" <+> text (show perm)
          , text "ps    =" <+> text (show ps)
          , text "body  =" <+> text (show body)
          , text "body  =" <+> prettyTCM body
          ]
        ]

      return $
        Clause { clauseRange = getRange i
               , clauseTel   = killRange delta
               , clausePerm  = perm
               , clausePats  = ps
               , clauseBody  = body
               }

checkClause t (A.Clause (A.LHS _ _ ps@(_ : _)) _ _) = typeError $ UnexpectedWithPatterns ps

checkWithFunction :: WithFunctionProblem -> TCM ()
checkWithFunction NoWithFunction = return ()
checkWithFunction (WithFunction f aux gamma delta1 delta2 vs as b qs perm' perm cs) = do

  reportSDoc "tc.with.top" 10 $ vcat
    [ text "checkWithFunction"
    , nest 2 $ vcat
      [ text "delta1 =" <+> prettyTCM delta1
      , text "delta2 =" <+> addCtxTel delta1 (prettyTCM delta2)
      , text "gamma  =" <+> prettyTCM gamma
      , text "as     =" <+> addCtxTel delta1 (prettyTCM as)
      , text "vs     =" <+> addCtxTel delta1 (prettyTCM vs)
      , text "b      =" <+> do addCtxTel delta1 $ addCtxTel delta2 $ prettyTCM b
      , text "qs     =" <+> text (show qs)
      , text "perm'  =" <+> text (show perm')
      , text "perm   =" <+> text (show perm)
      ]
    ]

  -- Add the type of the auxiliary function to the signature

  -- With display forms are closed
  df <- makeClosed <$> withDisplayForm f aux delta1 delta2 (size as) qs perm'

  reportSLn "tc.with.top" 20 "created with display form"

  -- Generate the type of the with function
  candidateType <- withFunctionType delta1 vs as delta2 b
  reportSDoc "tc.with.type" 10 $ sep [ text "candidate type:", nest 2 $ prettyTCM candidateType ]
  reportSDoc "tc.with.type" 50 $ sep [ text "candidate type:", nest 2 $ text $ show candidateType ]
  absAuxType <- withShowAllArguments
                $ disableDisplayForms
                $ dontReifyInteractionPoints
                $ reify candidateType
  reportSDoc "tc.with.type" 15 $
    vcat [ text "type of with function:"
         , nest 2 $ prettyTCM absAuxType
         ]
  reportSDoc "tc.with.type" 50 $
    vcat [ text "type of with function:"
         , nest 2 $ text $ show absAuxType
         ]
  -- The ranges in the generated type are completely bogus, so we kill them.
  auxType <- setCurrentRange (getRange cs)
               (traceCall NoHighlighting $  -- To avoid flicker.
                  isType_ $ killRange absAuxType)
    `catchError` \err -> case err of
      TypeError s e -> put s >> enterClosure e (traceCall (CheckWithFunctionType absAuxType) . typeError)
      _             -> throwError err

  case df of
    OpenThing _ (Display n ts dt) -> reportSDoc "tc.with.top" 20 $ text "Display" <+> fsep
      [ text (show n)
      , prettyList $ map prettyTCM ts
      , prettyTCM dt
      ]
  addConstant aux (Defn Relevant aux auxType [] [] [df] 0 noCompiledRep Axiom)
  solveSizeConstraints

  reportSDoc "tc.with.top" 10 $ sep
    [ text "added with function" <+> (prettyTCM aux) <+> text "of type"
    , nest 2 $ prettyTCM auxType
    , nest 2 $ text "-|" <+> (prettyTCM =<< getContextTelescope)
    ]

  -- Construct the body for the with function
  cs <- buildWithFunction aux gamma qs perm (size delta1) (size as) cs

  -- Check the with function
  checkFunDef NotDelayed info aux cs

  where
    info = Info.mkDefInfo (nameConcrete $ qnameName aux) defaultFixity' PublicAccess ConcreteDef (getRange cs)

-- | Type check a where clause. The first argument is the number of variables
--   bound in the left hand side.
checkWhere :: Nat -> [A.Declaration] -> TCM a -> TCM a
checkWhere _ []                      ret = ret
checkWhere n [A.ScopedDecl scope ds] ret = withScope_ scope $ checkWhere n ds ret
checkWhere n [A.Section _ m tel ds]  ret = do
  checkTelescope_ tel $ \tel' -> do
    reportSDoc "tc.def.where" 10 $
      text "adding section:" <+> prettyTCM m <+> text (show (size tel')) <+> text (show n)
    addSection m (size tel' + n)  -- the variables bound in the lhs
                                  -- are also parameters
    verboseS "tc.def.where" 10 $ do
      dx   <- prettyTCM m
      dtel <- mapM prettyA tel
      dtel' <- prettyTCM =<< lookupSection m
      reportSLn "" 0 $ "checking where section " ++ show dx ++ " " ++ show dtel
      reportSLn "" 0 $ "        actual tele: " ++ show dtel'
    withCurrentModule m $ checkDecls ds >> ret
checkWhere _ _ _ = __IMPOSSIBLE__

-- | Check if a pattern contains an absurd pattern. For instance, @suc ()@
containsAbsurdPattern :: A.Pattern -> Bool
containsAbsurdPattern p = case p of
    A.AbsurdP _   -> True
    A.VarP _      -> False
    A.WildP _     -> False
    A.ImplicitP _ -> False
    A.DotP _ _    -> False
    A.LitP _      -> False
    A.AsP _ _ p   -> containsAbsurdPattern p
    A.ConP _ _ ps -> any (containsAbsurdPattern . namedThing . unArg) ps
    A.DefP _ _ _  -> __IMPOSSIBLE__
    A.PatternSynP _ _ _ -> __IMPOSSIBLE__ -- False

actualConstructor :: QName -> TCM QName
actualConstructor c = do
    v <- constructorForm =<< normalise (Con c [])
    case ignoreSharing v of
        Con c _ -> return c
        _       -> actualConstructor =<< stripLambdas v
    where
        stripLambdas v = case ignoreSharing v of
            Con c _ -> return c
            Lam h b -> do
                x <- freshName_ $ absName b
                addCtx x (Dom h Relevant $ sort Prop) $ stripLambdas (absBody b)
            _       -> typeError $ GenericError $ "Not a constructor: " ++ show c
