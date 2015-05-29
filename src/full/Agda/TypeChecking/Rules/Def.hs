{-# LANGUAGE CPP #-}
{-# LANGUAGE PatternGuards #-}

module Agda.TypeChecking.Rules.Def where

import Prelude hiding (mapM)
import Control.Arrow ((***))
import Control.Applicative
import Control.Monad.State hiding (forM, mapM)
import Control.Monad.Reader hiding (forM, mapM)

import Data.Function
import Data.List hiding (sort)
import Data.Maybe
import Data.Traversable

import Agda.Syntax.Common
import Agda.Syntax.Position
import qualified Agda.Syntax.Abstract as A
import Agda.Syntax.Internal as I
import qualified Agda.Syntax.Info as Info
import Agda.Syntax.Fixity
import Agda.Syntax.Translation.InternalToAbstract
import Agda.Syntax.Info

import Agda.TypeChecking.Monad
import Agda.TypeChecking.Monad.Builtin (primRefl, primEqualityName)
import qualified Agda.TypeChecking.Monad.Benchmark as Bench

import Agda.TypeChecking.Constraints
import Agda.TypeChecking.Conversion
import Agda.TypeChecking.MetaVars
import Agda.TypeChecking.Reduce
import Agda.TypeChecking.Patterns.Abstract (expandPatternSynonyms)
import Agda.TypeChecking.Pretty
import Agda.TypeChecking.Substitute
import Agda.TypeChecking.Free
import Agda.TypeChecking.CheckInternal (checkType)
import Agda.TypeChecking.With
import Agda.TypeChecking.Telescope
import Agda.TypeChecking.Injectivity
import Agda.TypeChecking.Irrelevance
import Agda.TypeChecking.SizedTypes.Solve
import Agda.TypeChecking.RecordPatterns
import Agda.TypeChecking.CompiledClause (CompiledClauses(..))
import Agda.TypeChecking.CompiledClause.Compile

import Agda.TypeChecking.Rules.Term                ( checkExpr, inferExpr, inferExprForWith, checkDontExpandLast, checkTelescope, ConvColor(..) )
import Agda.TypeChecking.Rules.LHS                 ( checkLeftHandSide, LHSResult(..) )
import {-# SOURCE #-} Agda.TypeChecking.Rules.Decl ( checkDecls )

import Agda.Utils.Except ( MonadError(catchError, throwError) )
import Agda.Utils.Lens
import Agda.Utils.Size
import Agda.Utils.Permutation
import Agda.Utils.Monad

#include "undefined.h"
import Agda.Utils.Impossible

---------------------------------------------------------------------------
-- * Definitions by pattern matching
---------------------------------------------------------------------------

checkFunDef :: Delayed -> Info.DefInfo -> QName -> [A.Clause] -> TCM ()
checkFunDef delayed i name cs = do
        -- Get the type and relevance of the function
        t    <- typeOfConst name
        info  <- flip setRelevance defaultArgInfo <$> relOfConst name
        case isAlias cs t of
          Just (e, x) ->
            traceCall (CheckFunDef (getRange i) (qnameName name) cs) $ do
              -- Andreas, 2012-11-22: if the alias is in an abstract block
              -- it has been frozen.  We unfreeze it to enable type inference.
              -- See issue 729.
              whenM (isFrozen x) $ unfreezeMeta x
              checkAlias t info delayed i name e
          _ -> checkFunDef' t info delayed Nothing Nothing i name cs

-- | A single clause without arguments and without type signature is an alias.
isAlias :: [A.Clause] -> Type -> Maybe (A.Expr, MetaId)
isAlias cs t =
        case trivialClause cs of
          -- if we have just one clause without pattern matching and
          -- without a type signature, then infer, to allow
          -- "aliases" for things starting with hidden abstractions
          Just e | Just x <- isMeta (ignoreSharing $ unEl t) -> Just (e, x)
          _ -> Nothing
  where
    isMeta (MetaV x _) = Just x
    isMeta _           = Nothing
    trivialClause [A.Clause (A.LHS i (A.LHSHead f []) []) (A.RHS e) []] = Just e
    trivialClause _ = Nothing

-- | Check a trivial definition of the form @f = e@
checkAlias :: Type -> I.ArgInfo -> Delayed -> Info.DefInfo -> QName -> A.Expr -> TCM ()
checkAlias t' ai delayed i name e = do
  reportSDoc "tc.def.alias" 10 $ text "checkAlias" <+> vcat
    [ text (show name) <+> colon  <+> prettyTCM t'
    , text (show name) <+> equals <+> prettyTCM e
    ]

{-
  -- Infer the type of the rhs
  (v, t) <- applyRelevanceToContext (argInfoRelevance ai) $
                                    inferOrCheck e (Just t')
  -- v <- coerce v t t'
-}

  -- Infer the type of the rhs
  v <- applyRelevanceToContext (getRelevance ai) $ checkDontExpandLast e t'
  let t = t'

  reportSDoc "tc.def.alias" 20 $ text "checkAlias: finished checking"

  solveSizeConstraints

  v <- instantiateFull v  -- if we omit this, we loop (stdlib: Relation.Binary.Sum)
    -- or the termination checker might stumble over levels in sorts
    -- that cannot be converted to expressions without the level built-ins
    -- (test/succeed/Issue655.agda)

  -- Add the definition
  addConstant name $ defaultDefn ai name t
                   $ Function
                      { funClauses        = [ Clause  -- trivial clause @name = v@
                          { clauseRange     = getRange i
                          , clauseTel       = EmptyTel
                          , clausePerm      = idP 0
                          , namedClausePats = []
                          , clauseBody      = Body v
                          , clauseType      = Just $ Arg ai t
                          } ]
                      , funCompiled       = Just $ Done [] v
                      , funDelayed        = delayed
                      , funInv            = NotInjective
                      , funAbstr          = Info.defAbstract i
                      , funMutual         = []
                      , funProjection     = Nothing
                      , funStatic         = False
                      , funCopy           = False
                      , funTerminates     = Nothing
                      , funExtLam         = Nothing
                      , funWith           = Nothing
                      , funCopatternLHS   = False
                      }
  reportSDoc "tc.def.alias" 20 $ text "checkAlias: leaving"


-- | Type check a definition by pattern matching.
checkFunDef' :: Type             -- ^ the type we expect the function to have
             -> I.ArgInfo        -- ^ is it irrelevant (for instance)
             -> Delayed          -- ^ are the clauses delayed (not unfolded willy-nilly)
             -> Maybe (Int, Int) -- ^ does the definition come from an extended lambda
                                 --   (if so, we need to know some stuff about lambda-lifted args)
             -> Maybe QName      -- ^ is it a with function (if so, what's the name of the parent function)
             -> Info.DefInfo     -- ^ range info
             -> QName            -- ^ the name of the function
             -> [A.Clause]       -- ^ the clauses to check
             -> TCM ()
checkFunDef' t ai delayed extlam with i name cs =

    traceCall (CheckFunDef (getRange i) (qnameName name) cs) $ do   -- TODO!! (qnameName)
        reportSDoc "tc.def.fun" 10 $
          sep [ text "checking body of" <+> prettyTCM name
              , nest 2 $ text ":" <+> prettyTCM t
              , nest 2 $ text "full type:" <+> (prettyTCM . defType =<< getConstInfo name)
              ]

        cs <- return $ map A.lhsToSpine cs

        -- Ensure that all clauses have the same number of trailing hidden patterns
        -- This is necessary since trailing implicits are no longer eagerly inserted.
        -- Andreas, 2013-10-13
        -- Since we have flexible function arity, it is no longer necessary
        -- to patch clauses to same arity
        -- cs <- trailingImplicits t cs

        -- Check the clauses
        cs <- traceCall NoHighlighting $ do -- To avoid flicker.
            forM cs $ \ c -> do
              c <- applyRelevanceToContext (argInfoRelevance ai) $ do
                checkClause t c
              -- Andreas, 2013-11-23 do not solve size constraints here yet
              -- in case we are checking the body of an extended lambda.
              -- 2014-04-24: The size solver requires each clause to be
              -- checked individually, since otherwise we get constraints
              -- in typing contexts which are not prefixes of each other.
              unless (isJust extlam) $ solveSizeConstraints
              -- Andreas, 2013-10-27 add clause as soon it is type-checked
              -- TODO: instantiateFull?
              addClauses name [c]
              return c

        -- After checking, remove the clauses again.
        -- (Otherwise, @checkInjectivity@ loops for issue 801).
        modifyFunClauses name (const [])

        -- Check that all clauses have the same number of arguments
        -- unless (allEqual $ map npats cs) $ typeError DifferentArities
        -- Andreas, 2013-03-15 disable this check to allow flexible arity (issue 727)

        reportSDoc "tc.cc" 25 $ do
          sep [ text "clauses before injectivity test"
              , nest 2 $ prettyTCM $ map (QNamed name) cs  -- broken, reify (QNamed n cl) expect cl to live at top level
              ]
        reportSDoc "tc.cc" 60 $ do
          sep [ text "raw clauses: "
              , nest 2 $ sep $ map (text . show . QNamed name) cs
              ]

        -- Annotate the clauses with which arguments are actually used.
        cs <- instantiateFull {- =<< mapM rebindClause -} cs
        -- Andreas, 2010-11-12
        -- rebindClause is the identity, and instantiateFull eta-contracts
        -- removing this eta-contraction fixes issue 361
        -- however, Data.Star.Decoration.gmapAll no longer type-checks
        -- possibly due to missing eta-contraction!?

        -- Check if the function is injective
        reportSLn "tc.inj.def" 20 $ "checkFunDef': checking injectivity..."
        inv <- Bench.billTo [Bench.Injectivity] $
          checkInjectivity name cs
        -- inv <- return NotInjective

        reportSDoc "tc.cc" 15 $ do
          sep [ text "clauses before compilation"
              , nest 2 $ sep $ map (prettyTCM . QNamed name) cs
              ]

        -- add clauses for the coverage checker (needs to reduce)
        addClauses name cs

        -- Coverage check and compile the clauses
        cc <- Bench.billTo [Bench.Coverage] $
          compileClauses (Just (name, t)) cs

        reportSDoc "tc.cc" 10 $ do
          sep [ text "compiled clauses of" <+> prettyTCM name
              , nest 2 $ text (show cc)
              ]

        -- Add the definition
        addConstant name =<< do
          -- If there was a pragma for this definition, we can set the
          -- funTerminates field directly.
          useTerPragma $ defaultDefn ai name t $
             Function
             { funClauses        = cs
             , funCompiled       = Just cc
             , funDelayed        = delayed
             , funInv            = inv
             , funAbstr          = Info.defAbstract i
             , funMutual         = []
             , funProjection     = Nothing
             , funStatic         = False
             , funCopy           = False
             , funTerminates     = Nothing
             , funExtLam         = extlam
             , funWith           = with
             , funCopatternLHS   = isCopatternLHS cs
             }

        -- Andreas 2012-02-13: postpone polarity computation until after positivity check
        -- computePolarity name

        reportSDoc "tc.def.fun" 10 $ do
          sep [ text "added " <+> prettyTCM name <+> text ":"
              , nest 2 $ prettyTCM . defType =<< getConstInfo name
              ]
    where
        npats = size . clausePats

-- | Set 'funTerminates' according to termination info in 'TCEnv',
--   which comes from a possible termination pragma.
useTerPragma :: Definition -> TCM Definition
useTerPragma def@Defn{ defName = name, theDef = fun@Function{}} = do
  tc <- asks envTerminationCheck
  let terminates = case tc of
        NonTerminating -> Just False
        Terminating    -> Just True
        _              -> Nothing
  reportSLn "tc.fundef" 30 $ unlines $
    [ "funTerminates of " ++ show name ++ " set to " ++ show terminates
    , "  tc = " ++ show tc
    ]
  return $ def { theDef = fun { funTerminates = terminates }}
useTerPragma def = return def


-- | Insert some patterns in the in with-clauses LHS of the given RHS
insertPatterns :: [A.Pattern] -> A.RHS -> A.RHS
insertPatterns pats (A.WithRHS aux es cs) = A.WithRHS aux es (map insertToClause cs)
    where insertToClause (A.Clause (A.LHS i lhscore ps) rhs ds)
              = A.Clause (A.LHS i lhscore (pats ++ ps)) (insertPatterns pats rhs) ds
insertPatterns pats (A.RewriteRHS qes rhs wh) = A.RewriteRHS qes (insertPatterns pats rhs) wh
insertPatterns pats rhs = rhs

-- | Parameters for creating a @with@-function.
data WithFunctionProblem
  = NoWithFunction
  | WithFunction
    { wfParentName :: QName                -- ^ Parent function name.
    , wfName       :: QName                -- ^ With function name.
    , wfParentType :: Type                 -- ^ Type of the parent function.
    , wfBeforeTel  :: Telescope            -- ^ Types of arguments to the with function before the with expressions (needed vars).
    , wfAfterTel   :: Telescope            -- ^ Types of arguments to the with function after the with expressions (unneeded vars).
    , wfExprs      :: [Term]               -- ^ With expressions.
    , wfExprTypes  :: [Type]               -- ^ Types of the with expressions.
    , wfRHSType    :: Type                 -- ^ Type of the right hand side.
    , wfParentPats :: [I.NamedArg Pattern] -- ^ Parent patterns.
    , wfPermSplit  :: Permutation          -- ^ Permutation resulting from splitting the telescope into needed and unneeded vars.
    , wfPermParent :: Permutation          -- ^ Permutation reordering the variables in the parent pattern.
    , wfPermFinal  :: Permutation          -- ^ Final permutation (including permutation for the parent clause).
    , wfClauses    :: [A.Clause]           -- ^ The given clauses for the with function
    }

-- | Type check a function clause.
checkClause :: Type -> A.SpineClause -> TCM Clause
checkClause t c@(A.Clause (A.SpineLHS i x aps withPats) rhs0 wh) = do
    unless (null withPats) $
      typeError $ UnexpectedWithPatterns withPats
    traceCall (CheckClause t c) $ do
      aps <- expandPatternSynonyms aps
      checkLeftHandSide (CheckPatternShadowing c) (Just x) aps t $ \ (LHSResult delta ps trhs perm) -> do
        -- Note that we might now be in irrelevant context,
        -- in case checkLeftHandSide walked over an irrelevant projection pattern.

        -- As we will be type-checking the @rhs@ in @delta@, but the final
        -- body should have bindings in the order of the pattern variables,
        -- we need to apply the permutation to the checked rhs @v@.
        let mkBody v  = foldr (\ x t -> Bind $ Abs x t) b xs
             where b  = Body $ applySubst (renamingR perm) v
                   xs = [ stringToArgName $ "h" ++ show n
                          | n <- [0..permRange perm - 1] ]

        -- introduce trailing implicits for checking the where decls
        TelV htel t0 <- telViewUpTo' (-1) (not . visible) $ unArg trhs
        let n = size htel
            aps' = convColor aps
            checkWhere' wh = addCtxTel htel . checkWhere (size delta + n) wh . escapeContext (size htel)
        (body, with) <- checkWhere' wh $ let
            -- for the body, we remove the implicits again
            handleRHS rhs =
                case rhs of
                  A.RHS e
                    | any (containsAbsurdPattern . namedArg) aps ->
                      typeError $ AbsurdPatternRequiresNoRHS aps'
                    | otherwise -> do
                      v <- checkExpr e $ unArg trhs
                      return (mkBody v, NoWithFunction)
                  A.AbsurdRHS
                    | any (containsAbsurdPattern . namedArg) aps
                                -> return (NoBody, NoWithFunction)
                    | otherwise -> typeError $ NoRHSRequiresAbsurdPattern aps'
                  A.RewriteRHS [] rhs [] -> handleRHS rhs
                  -- Andreas, 2014-01-17, Issue 1402:
                  -- If the rewrites are discarded since lhs=rhs, then
                  -- we can actually have where clauses.
                  A.RewriteRHS [] rhs wh -> checkWhere' wh $ handleRHS rhs
                  A.RewriteRHS ((qname,eq):qes) rhs wh -> do

                       -- Action for skipping this rewrite.
                       -- We do not want to create unsolved metas in case of
                       -- a futile rewrite with a reflexive equation.
                       -- Thus, we restore the state in this case,
                       -- unless the rewrite expression contains questionmarks.
                       st <- get
                       let recurse = do
                            st' <- get
                            -- Comparing the whole stInteractionPoints maps is a bit
                            -- wasteful, but we assume
                            -- 1. rewriting with a reflexive equality to happen rarely,
                            -- 2. especially with ?-holes in the rewrite expression
                            -- 3. and a large overall number of ?s.
                            let sameIP = (==) `on` (^.stInteractionPoints)
                            when (sameIP st st') $ put st
                            handleRHS $ A.RewriteRHS qes rhs wh

                       -- Get value and type of rewrite-expression.

                       (proof,t) <- inferExpr eq

                       -- Get the names of builtins EQUALITY and REFL.

                       equality <- primEqualityName
                       Con reflCon [] <- ignoreSharing <$> primRefl

                       -- Check that the type is actually an equality (lhs ≡ rhs)
                       -- and extract lhs, rhs, and their type.

                       t' <- reduce =<< instantiateFull t
                       (rewriteType,rewriteFrom,rewriteTo) <- do
                         case ignoreSharing $ unEl t' of
                           Def equality'
                             [ _level
                             , Apply (Arg (ArgInfo Hidden    Relevant _) rewriteType)
                             , Apply (Arg (ArgInfo NotHidden Relevant _) rewriteFrom)
                             , Apply (Arg (ArgInfo NotHidden Relevant _) rewriteTo)
                             ] | equality' == equality ->
                                 return (El (getSort t') rewriteType, rewriteFrom, rewriteTo)
                           _ -> do
                            err <- text "Cannot rewrite by equation of type" <+> prettyTCM t'
                            typeError $ GenericDocError err

                       -- Andreas, 2014-05-17  Issue 1110:
                       -- Rewriting with a reflexive equation has no effect, but gives an
                       -- incomprehensible error message about the generated
                       -- with clause. Thus, we rather do simply nothing if
                       -- rewriting with @a ≡ a@ is attempted.

                       let isReflexive = tryConversion $ dontAssignMetas $
                            equalTerm rewriteType rewriteFrom rewriteTo

                       ifM isReflexive recurse $ {- else -} do

                         -- Transform 'rewrite' clause into a 'with' clause,
                         -- going back to abstract syntax.

                         let cinfo      = ConPatInfo False patNoRange
                             underscore = A.Underscore Info.emptyMetaInfo

                         -- Andreas, 2015-02-09 Issue 1421: kill ranges
                         -- as reify puts in ranges that may point to other files.
                         (rewriteFromExpr,rewriteToExpr,rewriteTypeExpr, proofExpr) <- killRange <$> do
                          disableDisplayForms $ withShowAllArguments $ reify
                            (rewriteFrom,   rewriteTo,    rewriteType    , proof)
                         let (inner, outer) -- the where clauses should go on the inner-most with
                               | null qes  = ([], wh)
                               | otherwise = (wh, [])
                             -- Andreas, 2014-03-05 kill range of copied patterns
                             -- since they really do not have a source location.
                             newRhs = A.WithRHS qname [rewriteFromExpr, proofExpr]
                                      [A.Clause (A.LHS i (A.LHSHead x (killRange aps)) pats)
                                        -- Note: handleRHS (A.RewriteRHS _ eqs _ _)
                                        -- is defined by induction on eqs.
                                        (A.RewriteRHS qes (insertPatterns pats rhs) inner)
                                        outer]
                             pats = [ A.DotP patNoRange underscore
                                    , A.ConP cinfo (AmbQ [conName reflCon]) []]
                         reportSDoc "tc.rewrite.top" 25 $ vcat
                           [ text "rewrite"
                           , text "  from  = " <+> prettyTCM rewriteFromExpr
                           , text "  to    = " <+> prettyTCM rewriteToExpr
                           , text "  typ   = " <+> prettyTCM rewriteType
                           , text "  proof = " <+> prettyTCM proofExpr
                           , text "  equ   = " <+> prettyTCM t'
                           ]
                         handleRHS newRhs

                  A.WithRHS aux es cs -> do
                    reportSDoc "tc.with.top" 15 $ vcat
                      [ text "TC.Rules.Def.checkclause reached A.WithRHS"
                      , sep $ prettyA aux : map (parens . prettyA) es
                      ]
                    reportSDoc "tc.with.top" 30 $
                      prettyA c
                    reportSDoc "tc.with.top" 20 $ do
                      m  <- currentModule
                      nfv <- getModuleFreeVars m
                      sep [ text "with function module:" <+>
                            prettyList (map prettyTCM $ mnameToList m)
                          ,  text $ "free variables: " ++ show nfv
                          ]

                    -- Infer the types of the with expressions
                    (vs0, as) <- unzip <$> mapM inferExprForWith es
                    (vs, as)  <- normalise (vs0, as)

                    -- Split the telescope into the part needed to type the with arguments
                    -- and all the other stuff
                    let fv = allFreeVars (vs, as)
                        SplitTel delta1 delta2 perm' = splitTelescope fv delta
                        finalPerm = composeP perm' perm

                    reportSLn "tc.with.top" 75 $ "delta  = " ++ show delta

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

                    -- All the context variables
                    us <- getContextArgs
                    let n = size us
                        m = size delta
                        -- First the variables bound outside this definition
                        (us0, us1') = genericSplitAt (n - m) us
                        -- Then permute the rest and grab those needed to for the with arguments
                        (us1, us2)  = genericSplitAt (size delta1) $ permute perm' us1'
                        -- Now stuff the with arguments in between and finish with the remaining variables
                        v    = Def aux $ map Apply $ us0 ++ us1 ++ (map defaultArg vs0) ++ us2

                    -- We need Δ₁Δ₂ ⊢ t'
                    t' <- return $ renameP (reverseP perm') $ unArg trhs
                    -- and Δ₁ ⊢ vs : as
                    (vs, as) <- do
                      let -- We know that as does not depend on Δ₂
                          rho = compactS __IMPOSSIBLE__ (replicate (size delta2) Nothing)
                      return $ applySubst rho $ renameP (reverseP perm') (vs, as)


                    -- Andreas, 2013-02-26 add with-name to signature for printing purposes
                    addConstant aux =<< do
                      useTerPragma $ Defn defaultArgInfo aux typeDontCare [] [] [] 0 noCompiledRep [] Nothing emptyFunction

                    -- Andreas, 2013-02-26 separate msgs to see which goes wrong
                    reportSDoc "tc.with.top" 20 $
                      text "    with arguments" <+> do escapeContext (size delta2) $ prettyList (map prettyTCM vs)
                    reportSDoc "tc.with.top" 20 $
                      text "             types" <+> do escapeContext (size delta2) $ prettyList (map prettyTCM as)
                    reportSDoc "tc.with.top" 20 $
                      text "with function call" <+> prettyTCM v
                    reportSDoc "tc.with.top" 20 $
                      text "           context" <+> (prettyTCM =<< getContextTelescope)
                    reportSDoc "tc.with.top" 20 $
                      text "             delta" <+> do escapeContext (size delta) $ prettyTCM delta
                    reportSDoc "tc.with.top" 20 $
                      text "                fv" <+> text (show fv)
                    reportSDoc "tc.with.top" 20 $
                      text "              body" <+> (addCtxTel delta $ prettyTCM $ mkBody v)

                    return (mkBody v, WithFunction x aux t delta1 delta2 vs as t' ps perm' perm finalPerm cs)
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
          Clause { clauseRange     = getRange i
                 , clauseTel       = killRange delta
                 , clausePerm      = perm
                 , namedClausePats = ps
                 , clauseBody      = body
                 , clauseType      = Just trhs
                 }


checkWithFunction :: WithFunctionProblem -> TCM ()
checkWithFunction NoWithFunction = return ()
checkWithFunction (WithFunction f aux t delta1 delta2 vs as b qs perm' perm finalPerm cs) = do

  reportSDoc "tc.with.top" 10 $ vcat
    [ text "checkWithFunction"
    , nest 2 $ vcat
      [ text "delta1 =" <+> prettyTCM delta1
      , text "delta2 =" <+> addCtxTel delta1 (prettyTCM delta2)
      , text "t      =" <+> prettyTCM t
      , text "as     =" <+> addCtxTel delta1 (prettyTCM as)
      , text "vs     =" <+> addCtxTel delta1 (prettyTCM vs)
      , text "b      =" <+> do addCtxTel delta1 $ addCtxTel delta2 $ prettyTCM b
      , text "qs     =" <+> text (show qs)
      , text "perm'  =" <+> text (show perm')
      , text "perm   =" <+> text (show perm)
      , text "fperm   =" <+> text (show finalPerm)
      ]
    ]

  -- Add the type of the auxiliary function to the signature

  -- With display forms are closed
  df <- makeClosed <$> withDisplayForm f aux delta1 delta2 (size as) qs perm' perm

  reportSLn "tc.with.top" 20 "created with display form"

  -- Generate the type of the with function
  delta1 <- normalise delta1 -- Issue 1332: checkInternal is picky about argInfo
                             -- but module application is sloppy.
                             -- We normalise to get rid of Def's coming
                             -- from module applications.
  candidateType <- withFunctionType delta1 vs as delta2 b
  reportSDoc "tc.with.type" 10 $ sep [ text "candidate type:", nest 2 $ prettyTCM candidateType ]
  reportSDoc "tc.with.type" 50 $ sep [ text "candidate type:", nest 2 $ text $ show candidateType ]

{- OLD, going through abstract syntax

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
  auxType <- setCurrentRange cs
               (traceCall NoHighlighting $  -- To avoid flicker.
                  isType_ $ killRange absAuxType)
    `catchError` \err -> case err of
      TypeError s e -> put s >> enterClosure e (traceCall (CheckWithFunctionType absAuxType) . typeError)
      _             -> throwError err
-}
  -- Andreas, 2013-10-21
  -- Check generated type directly in internal syntax.
  absAuxType <- reify candidateType
  let auxType = candidateType
  setCurrentRange cs
    (traceCall NoHighlighting $   -- To avoid flicker.
      checkType auxType)
    `catchError` \err -> case err of
      TypeError s e -> do
        put s
        enterClosure e $ do
          traceCall (CheckWithFunctionType absAuxType) . typeError
      err           -> throwError err

  case df of
    OpenThing _ (Display n ts dt) -> reportSDoc "tc.with.top" 20 $ text "Display" <+> fsep
      [ text (show n)
      , prettyList $ map prettyTCM ts
      , prettyTCM dt
      ]
  addConstant aux =<< do
    useTerPragma $ Defn defaultArgInfo aux auxType [] [] [df] 0 noCompiledRep [] Nothing emptyFunction
  -- solveSizeConstraints -- Andreas, 2012-10-16 does not seem necessary

  reportSDoc "tc.with.top" 10 $ sep
    [ text "added with function" <+> (prettyTCM aux) <+> text "of type"
    , nest 2 $ prettyTCM auxType
    , nest 2 $ text "-|" <+> (prettyTCM =<< getContextTelescope)
    ]

  -- Construct the body for the with function
  cs <- return $ map (A.lhsToSpine) cs
  cs <- buildWithFunction aux t qs finalPerm (size delta1) (size as) cs
  cs <- return $ map (A.spineToLhs) cs

  -- Check the with function
  checkFunDef' auxType defaultArgInfo NotDelayed Nothing (Just f) info aux cs

  where
    info = Info.mkDefInfo (nameConcrete $ qnameName aux) defaultFixity' PublicAccess ConcreteDef (getRange cs)

-- | Type check a where clause. The first argument is the number of variables
--   bound in the left hand side.
checkWhere :: Nat -> [A.Declaration] -> TCM a -> TCM a
checkWhere _ []                      ret = ret
checkWhere n [A.ScopedDecl scope ds] ret = withScope_ scope $ checkWhere n ds ret
checkWhere n [A.Section _ m tel ds]  ret = do
  checkTelescope tel $ \ tel' -> do
    reportSDoc "tc.def.where" 10 $
      text "adding section:" <+> prettyTCM m <+> text (show (size tel')) <+> text (show n)
    addSection m (size tel' + n)  -- the variables bound in the lhs
                                  -- are also parameters
    verboseS "tc.def.where" 10 $ do
      dx   <- prettyTCM m
      dtel <- mapM prettyAs tel
      dtel' <- prettyTCM =<< lookupSection m
      reportSLn "tc.def.where" 10 $ "checking where section " ++ show dx ++ " " ++ show dtel
      reportSLn "tc.def.where" 10 $ "        actual tele: " ++ show dtel'
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
    A.ConP _ _ ps -> any (containsAbsurdPattern . namedArg) ps
    A.DefP _ _ _  -> False  -- projection pattern
    A.PatternSynP _ _ _ -> __IMPOSSIBLE__ -- False
