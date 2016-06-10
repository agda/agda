{-# LANGUAGE CPP                      #-}
{-# LANGUAGE NondecreasingIndentation #-}

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
import Agda.Syntax.Concrete (exprFieldA)
import Agda.Syntax.Position
import qualified Agda.Syntax.Abstract as A
import Agda.Syntax.Internal as I
import Agda.Syntax.Internal.Pattern as I
import qualified Agda.Syntax.Info as Info
import Agda.Syntax.Fixity
import Agda.Syntax.Translation.InternalToAbstract
import Agda.Syntax.Info

import Agda.TypeChecking.Monad
import Agda.TypeChecking.Monad.Builtin
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

import Agda.TypeChecking.Rules.Term                ( checkExpr, inferExpr, inferExprForWith, checkDontExpandLast, checkTelescope )
import Agda.TypeChecking.Rules.LHS                 ( checkLeftHandSide, LHSResult(..), bindAsPatterns )
import Agda.TypeChecking.Rules.LHS.Problem         ( AsBinding(..) )
import {-# SOURCE #-} Agda.TypeChecking.Rules.Decl ( checkDecls )

import Agda.Utils.Except ( MonadError(catchError, throwError) )
import Agda.Utils.Lens
import Agda.Utils.Maybe ( whenNothing )
import Agda.Utils.Monad
import Agda.Utils.Permutation
import Agda.Utils.Size
import Agda.Utils.Functor

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
    trivialClause [A.Clause (A.LHS i (A.LHSHead f []) []) _ (A.RHS e) [] _] = Just e
    trivialClause _ = Nothing

-- | Check a trivial definition of the form @f = e@
checkAlias :: Type -> ArgInfo -> Delayed -> Info.DefInfo -> QName -> A.Expr -> TCM ()
checkAlias t' ai delayed i name e = atClause name 0 $ do
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

  solveSizeConstraints DontDefaultToInfty

  v <- instantiateFull v  -- if we omit this, we loop (stdlib: Relation.Binary.Sum)
    -- or the termination checker might stumble over levels in sorts
    -- that cannot be converted to expressions without the level built-ins
    -- (test/succeed/Issue655.agda)

  -- compute body modification for irrelevant definitions, see issue 610
  let bodyMod = case getRelevance ai of
        Irrelevant -> dontCare
        _          -> id

  -- Add the definition
  addConstant name $ defaultDefn ai name t
                   $ Function
                      { funClauses        = [ Clause  -- trivial clause @name = v@
                          { clauseRange     = getRange i
                          , clauseTel       = EmptyTel
                          , namedClausePats = []
                          , clauseBody      = Body $ bodyMod v
                          , clauseType      = Just $ Arg ai t
                          , clauseCatchall  = False
                          } ]
                      , funCompiled       = Just $ Done [] $ bodyMod v
                      , funTreeless       = Nothing
                      , funDelayed        = delayed
                      , funInv            = NotInjective
                      , funAbstr          = Info.defAbstract i
                      , funMutual         = []
                      , funProjection     = Nothing
                      , funSmashable      = True
                      , funStatic         = False
                      , funInline         = False
                      , funTerminates     = Nothing
                      , funExtLam         = Nothing
                      , funWith           = Nothing
                      , funCopatternLHS   = False
                      }
  reportSDoc "tc.def.alias" 20 $ text "checkAlias: leaving"


-- | Type check a definition by pattern matching.
checkFunDef' :: Type             -- ^ the type we expect the function to have
             -> ArgInfo        -- ^ is it irrelevant (for instance)
             -> Delayed          -- ^ are the clauses delayed (not unfolded willy-nilly)
             -> Maybe ExtLamInfo -- ^ does the definition come from an extended lambda
                                 --   (if so, we need to know some stuff about lambda-lifted args)
             -> Maybe QName      -- ^ is it a with function (if so, what's the name of the parent function)
             -> Info.DefInfo     -- ^ range info
             -> QName            -- ^ the name of the function
             -> [A.Clause]       -- ^ the clauses to check
             -> TCM ()
checkFunDef' t ai delayed extlam with i name cs =
  checkFunDefS t ai delayed extlam with i name Nothing cs

-- | Type check a definition by pattern matching.
checkFunDefS :: Type             -- ^ the type we expect the function to have
             -> ArgInfo        -- ^ is it irrelevant (for instance)
             -> Delayed          -- ^ are the clauses delayed (not unfolded willy-nilly)
             -> Maybe ExtLamInfo -- ^ does the definition come from an extended lambda
                                 --   (if so, we need to know some stuff about lambda-lifted args)
             -> Maybe QName      -- ^ is it a with function (if so, what's the name of the parent function)
             -> Info.DefInfo     -- ^ range info
             -> QName            -- ^ the name of the function
             -> Maybe Substitution -- ^ substitution (from with abstraction) that needs to be applied to module parameters
             -> [A.Clause]       -- ^ the clauses to check
             -> TCM ()
checkFunDefS t ai delayed extlam with i name withSub cs =

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
            forM (zip cs [0..]) $ \ (c, clauseNo) -> atClause name clauseNo $ do
              c <- applyRelevanceToContext (argInfoRelevance ai) $ do
                checkClause t withSub c
              -- Andreas, 2013-11-23 do not solve size constraints here yet
              -- in case we are checking the body of an extended lambda.
              -- 2014-04-24: The size solver requires each clause to be
              -- checked individually, since otherwise we get constraints
              -- in typing contexts which are not prefixes of each other.
              whenNothing extlam $ solveSizeConstraints DontDefaultToInfty
              -- Andreas, 2013-10-27 add clause as soon it is type-checked
              -- TODO: instantiateFull?
              inTopContext $ addClauses name [c]
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

        -- Check if the function is injective.
        -- Andreas, 2015-07-01 we do it here in order to resolve metas
        -- in mutual definitions, e.g. the U/El definition in succeed/Issue439.agda
        -- We do it again for the mutual block after polarity analysis, see Rules.Decl.
        reportSLn "tc.inj.def" 20 $ "checkFunDef': checking injectivity..."
        inv <- Bench.billTo [Bench.Injectivity] $
          checkInjectivity name cs

        reportSDoc "tc.cc" 15 $ do
          sep [ text "clauses before compilation"
              , nest 2 $ sep $ map (prettyTCM . QNamed name) cs
              ]

        -- add clauses for the coverage checker (needs to reduce)
        inTopContext $ addClauses name cs

        fullType <- flip telePi t <$> getContextTelescope

        -- Coverage check and compile the clauses
        cc <- Bench.billTo [Bench.Coverage] $
          inTopContext $ compileClauses (Just (name, fullType)) cs

        reportSDoc "tc.cc" 10 $ do
          sep [ text "compiled clauses of" <+> prettyTCM name
              , nest 2 $ text (show cc)
              ]

        -- Add the definition
        inTopContext $ addConstant name =<< do
          -- If there was a pragma for this definition, we can set the
          -- funTerminates field directly.
          useTerPragma $ defaultDefn ai name fullType $
             Function
             { funClauses        = cs
             , funCompiled       = Just cc
             , funTreeless       = Nothing
             , funDelayed        = delayed
             , funInv            = inv
             , funAbstr          = Info.defAbstract i
             , funMutual         = []
             , funProjection     = Nothing
             , funSmashable      = True
             , funStatic         = False
             , funInline         = False
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
    where insertToClause (A.Clause (A.LHS i lhscore ps) dots rhs ds catchall)
              = A.Clause (A.LHS i lhscore (pats ++ ps)) dots (insertPatterns pats rhs) ds catchall
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
    , wfExprs      :: [Term]               -- ^ With and rewrite expressions.
    , wfExprTypes  :: [EqualityView]       -- ^ Types of the with and rewrite expressions.
    , wfRHSType    :: Type                 -- ^ Type of the right hand side.
    , wfParentPats :: [NamedArg Pattern]   -- ^ Parent patterns.
    , wfParentParams :: Nat                -- ^ Number of module parameters in parent patterns
    , wfPermSplit  :: Permutation          -- ^ Permutation resulting from splitting the telescope into needed and unneeded vars.
    , wfPermParent :: Permutation          -- ^ Permutation reordering the variables in the parent pattern.
    , wfPermFinal  :: Permutation          -- ^ Final permutation (including permutation for the parent clause).
    , wfClauses    :: [A.Clause]           -- ^ The given clauses for the with function
    }

-- | Create a clause body from a term.
--
--   As we have type checked the term in the clause telescope, but the final
--   body should have bindings in the order of the pattern variables,
--   we need to apply the permutation to the checked term.

mkBody :: Permutation -> Term -> ClauseBody
mkBody perm v = foldr (\ x t -> Bind $ Abs x t) b xs
  where
    b  = Body $ applySubst (renamingR perm) v
    xs = [ stringToArgName $ "h" ++ show n | n <- [0 .. permRange perm - 1] ]


-- | Type check a function clause.

checkClause
  :: Type          -- ^ Type of function defined by this clause.
  -> Maybe Substitution  -- ^ Module parameter substitution arising from with-abstraction.
  -> A.SpineClause -- ^ Clause.
  -> TCM Clause    -- ^ Type-checked clause.

checkClause t withSub c@(A.Clause (A.SpineLHS i x aps withPats) namedDots rhs0 wh catchall) = do
    reportSDoc "tc.lhs.top" 30 $ text "Checking clause" $$ prettyA c
    unless (null withPats) $
      typeError $ UnexpectedWithPatterns withPats
    traceCall (CheckClause t c) $ do
      aps <- expandPatternSynonyms aps
      cxtNames <- reverse . map (fst . unDom) <$> getContext
      when (not $ null namedDots) $ reportSDoc "tc.lhs.top" 50 $
        text "namedDots:" <+> vcat [ prettyTCM x <+> text "=" <+> prettyTCM v <+> text ":" <+> prettyTCM a | A.NamedDot x v a <- namedDots ]
      -- Not really an as-pattern, but this does the right thing.
      bindAsPatterns [ AsB x v a | A.NamedDot x v a <- namedDots ] $
        checkLeftHandSide (CheckPatternShadowing c) (Just x) aps t withSub $ \ lhsResult@(LHSResult npars delta ps trhs perm) -> do
        -- Note that we might now be in irrelevant context,
        -- in case checkLeftHandSide walked over an irrelevant projection pattern.
        (body, with) <- checkWhere (unArg trhs) wh $ checkRHS i x aps t lhsResult rhs0

        -- Note that the with function doesn't necessarily share any part of
        -- the context with the parent (but withSub will take you from parent
        -- to child).
        inTopContext $ checkWithFunction cxtNames with

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

        -- compute body modification for irrelevant definitions, see issue 610
        rel <- asks envRelevance
        let bodyMod body = case rel of
              Irrelevant -> dontCare <$> body
              _          -> body

        return $
          Clause { clauseRange     = getRange i
                 , clauseTel       = killRange delta
                 , namedClausePats = numberPatVars perm ps
                 , clauseBody      = bodyMod body
                 , clauseType      = Just trhs
                 , clauseCatchall  = catchall
                 }

-- | Type check the @with@ and @rewrite@ lhss and/or the rhs.

checkRHS
  :: LHSInfo                 -- ^ Range of lhs.
  -> QName                   -- ^ Name of function.
  -> [NamedArg A.Pattern]    -- ^ Patterns in lhs.
  -> Type                    -- ^ Type of function.
  -> LHSResult               -- ^ Result of type-checking patterns
  -> A.RHS                   -- ^ Rhs to check.
  -> TCM (ClauseBody, WithFunctionProblem)

checkRHS i x aps t lhsResult@(LHSResult _ delta ps trhs perm) rhs0 = handleRHS rhs0
  where
  absurdPat = any (containsAbsurdPattern . namedArg) aps
  handleRHS rhs =
    case rhs of

      -- Case: ordinary RHS
      A.RHS e -> do
        when absurdPat $ typeError $ AbsurdPatternRequiresNoRHS aps
        v <- checkExpr e $ unArg trhs
        return (mkBody perm v, NoWithFunction)

      -- Case: no RHS
      A.AbsurdRHS -> do
        unless absurdPat $ typeError $ NoRHSRequiresAbsurdPattern aps
        return (NoBody, NoWithFunction)

      -- Case: @rewrite@
      A.RewriteRHS [] rhs [] -> handleRHS rhs
      -- Andreas, 2014-01-17, Issue 1402:
      -- If the rewrites are discarded since lhs=rhs, then
      -- we can actually have where clauses.
      A.RewriteRHS [] rhs wh -> checkWhere (unArg trhs) wh $ handleRHS rhs
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

        (proof, eqt) <- inferExpr eq

        -- Andreas, 2016-04-14, see also Issue #1796
        -- Run the size constraint solver to improve with-abstraction
        -- in case the with-expression contains size metas.
        solveSizeConstraints DefaultToInfty

        -- Check that the type is actually an equality (lhs ≡ rhs)
        -- and extract lhs, rhs, and their type.

        t' <- reduce =<< instantiateFull eqt
        (eqt,rewriteType,rewriteFrom,rewriteTo) <- equalityView t' >>= \case
          eqt@(EqualityType s _eq _level dom a b) -> return (eqt, El s (unArg dom), unArg a, unArg b)
          OtherType{} -> typeError . GenericDocError =<< do
            text "Cannot rewrite by equation of type" <+> prettyTCM t'

        -- Get the name of builtin REFL.

        Con reflCon [] <- ignoreSharing <$> primRefl

        -- Andreas, 2014-05-17  Issue 1110:
        -- Rewriting with @refl@ has no effect, but gives an
        -- incomprehensible error message about the generated
        -- with clause. Thus, we rather do simply nothing if
        -- rewriting with @refl@ is attempted.

        let isReflProof = do
             v <- reduce proof
             case ignoreSharing v of
               Con c [] | c == reflCon -> return True
               _ -> return False

        ifM isReflProof recurse $ {- else -} do

        -- Process 'rewrite' clause like a suitable 'with' clause.

        let reflPat  = A.ConP (ConPatInfo ConPCon patNoRange) (AmbQ [conName reflCon]) []

        -- Andreas, 2015-12-25  Issue #1740:
        -- After the fix of #520, rewriting with a reflexive equation
        -- has to be desugared as matching against refl.
        let isReflexive = tryConversion $ dontAssignMetas $
             equalTerm rewriteType rewriteFrom rewriteTo

        (pats, withExpr, withType) <- do
          ifM isReflexive
            {-then-} (return ([ reflPat ], proof, OtherType t'))
            {-else-} (return ([ A.WildP patNoRange, reflPat ], proof, eqt))

        let rhs'     = insertPatterns pats rhs
            (rhs'', outerWhere) -- the where clauses should go on the inner-most with
              | null qes  = (rhs', wh)
              | otherwise = (A.RewriteRHS qes rhs' wh, [])
            -- Andreas, 2014-03-05 kill range of copied patterns
            -- since they really do not have a source location.
            cs       = [A.Clause (A.LHS i (A.LHSHead x (killRange aps)) pats) [] rhs'' outerWhere False]

        checkWithRHS x qname t lhsResult [withExpr] [withType] cs

      -- Case: @with@
      A.WithRHS aux es cs -> do
        reportSDoc "tc.with.top" 15 $ vcat
          [ text "TC.Rules.Def.checkclause reached A.WithRHS"
          , sep $ prettyA aux : map (parens . prettyA) es
          ]
        reportSDoc "tc.with.top" 20 $ do
          nfv <- getCurrentModuleFreeVars
          m   <- currentModule
          sep [ text "with function module:" <+>
                prettyList (map prettyTCM $ mnameToList m)
              ,  text $ "free variables: " ++ show nfv
              ]

        -- Infer the types of the with expressions
        (vs0, as) <- unzip <$> mapM inferExprForWith es

        -- Andreas, 2016-01-23, Issue #1796
        -- Run the size constraint solver to improve with-abstraction
        -- in case the with-expression contains size metas.
        solveSizeConstraints DefaultToInfty

        checkWithRHS x aux t lhsResult vs0 (map OtherType as) cs

checkWithRHS
  :: QName                   -- ^ Name of function.
  -> QName                   -- ^ Name of the with-function.
  -> Type                    -- ^ Type of function.
  -> LHSResult               -- ^ Result of type-checking patterns
  -> [Term]                  -- ^ With-expressions.
  -> [EqualityView]          -- ^ Types of with-expressions.
  -> [A.Clause]              -- ^ With-clauses to check.
  -> TCM (ClauseBody, WithFunctionProblem)

checkWithRHS x aux t (LHSResult npars delta ps trhs perm) vs0 as cs = do
        let withArgs = withArguments vs0 as
        (vs, as)  <- normalise (vs0, as)

        -- Andreas, 2012-09-17: for printing delta,
        -- we should remove it from the context first
        reportSDoc "tc.with.top" 25 $ escapeContext (size delta) $ vcat
          [ text "delta  =" <+> prettyTCM delta
          ]
        reportSDoc "tc.with.top" 25 $ vcat
          [ text "vs     =" <+> prettyTCM vs
          , text "as     =" <+> prettyTCM as
          , text "perm   =" <+> text (show perm)
          ]

        -- Split the telescope into the part needed to type the with arguments
        -- and all the other stuff
        (delta1, delta2, perm', t', as, vs) <- return $
          splitTelForWith delta (unArg trhs) as vs
        let finalPerm = composeP perm' perm

        reportSLn "tc.with.top" 75 $ "delta  = " ++ show delta

        -- Andreas, 2012-09-17: for printing delta,
        -- we should remove it from the context first
        reportSDoc "tc.with.top" 25 $ escapeContext (size delta) $ vcat
          [ text "delta1 =" <+> prettyTCM delta1
          , text "delta2 =" <+> addContext delta1 (prettyTCM delta2)
          ]
        reportSDoc "tc.with.top" 25 $ vcat
          [ text "perm'  =" <+> text (show perm')
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
            v    = Def aux $ map Apply $ us0 ++ us1 ++ map defaultArg withArgs ++ us2
            body = mkBody perm v
        -- Andreas, 2013-02-26 add with-name to signature for printing purposes
        addConstant aux =<< do
          useTerPragma $ defaultDefn defaultArgInfo aux typeDontCare emptyFunction

        -- Andreas, 2013-02-26 separate msgs to see which goes wrong
        reportSDoc "tc.with.top" 20 $
          text "    with arguments" <+> do escapeContext (size delta) $ addContext delta1 $ prettyList (map prettyTCM vs)
        reportSDoc "tc.with.top" 20 $
          text "             types" <+> do escapeContext (size delta) $ addContext delta1 $ prettyList (map prettyTCM as)
        reportSDoc "tc.with.top" 20 $
          text "with function call" <+> prettyTCM v
        reportSDoc "tc.with.top" 20 $
          text "           context" <+> (prettyTCM =<< getContextTelescope)
        reportSDoc "tc.with.top" 20 $
          text "             delta" <+> do escapeContext (size delta) $ prettyTCM delta
        reportSDoc "tc.with.top" 20 $
          text "            delta1" <+> do escapeContext (size delta) $ prettyTCM delta1
        reportSDoc "tc.with.top" 20 $
          text "            delta2" <+> do escapeContext (size delta) $ addContext delta1 $ prettyTCM delta2
        reportSDoc "tc.with.top" 20 $
          text "              body" <+> (addContext delta $ prettyTCM body)

        return (body, WithFunction x aux t delta1 delta2 vs as t' ps npars perm' perm finalPerm cs)

checkWithFunction :: [Name] -> WithFunctionProblem -> TCM ()
checkWithFunction _ NoWithFunction = return ()
checkWithFunction cxtNames (WithFunction f aux t delta1 delta2 vs as b qs npars perm' perm finalPerm cs) = do

  let -- Δ₁ ws Δ₂ ⊢ withSub : Δ′    (where Δ′ is the context of the parent lhs)
      withSub :: Substitution
      withSub = liftS (size delta2) (wkS (countWithArgs as) idS) `composeS` renaming (reverseP perm')

  reportSDoc "tc.with.top" 10 $ vcat
    [ text "checkWithFunction"
    , nest 2 $ vcat
      [ text "delta1 =" <+> prettyTCM delta1
      , text "delta2 =" <+> addContext delta1 (prettyTCM delta2)
      , text "t      =" <+> prettyTCM t
      , text "as     =" <+> addContext delta1 (prettyTCM as)
      , text "vs     =" <+> do addContext delta1 $ prettyTCM vs
      , text "b      =" <+> do addContext delta1 $ addContext delta2 $ prettyTCM b
      , text "qs     =" <+> text (show qs)
      , text "perm'  =" <+> text (show perm')
      , text "perm   =" <+> text (show perm)
      , text "fperm  =" <+> text (show finalPerm)
      , text "withSub=" <+> text (show withSub)
      ]
    ]

  -- Add the type of the auxiliary function to the signature

  -- Generate the type of the with function
  delta1 <- normalise delta1 -- Issue 1332: checkInternal is picky about argInfo
                             -- but module application is sloppy.
                             -- We normalise to get rid of Def's coming
                             -- from module applications.
  (withFunType, n) <- withFunctionType delta1 vs as delta2 b
  reportSDoc "tc.with.type" 10 $ sep [ text "with-function type:", nest 2 $ prettyTCM withFunType ]
  reportSDoc "tc.with.type" 50 $ sep [ text "with-function type:", nest 2 $ text $ show withFunType ]

  -- Andreas, 2013-10-21
  -- Check generated type directly in internal syntax.
  setCurrentRange cs
    (traceCall NoHighlighting $   -- To avoid flicker.
      checkType withFunType)
    `catchError` \err -> case err of
      TypeError s e -> do
        put s
        wt <- reify withFunType
        enterClosure e $ do
          traceCall (CheckWithFunctionType wt) . typeError
      err           -> throwError err

  -- With display forms are closed

  df <- makeGlobal =<< withDisplayForm f aux delta1 delta2 n qs perm' perm

  reportSLn "tc.with.top" 20 "created with display form"

  case dget df of
    Display n ts dt ->
      reportSDoc "tc.with.top" 20 $ text "Display" <+> fsep
        [ text (show n)
        , prettyList $ map prettyTCM ts
        , prettyTCM dt
        ]
  addConstant aux =<< do
    useTerPragma $ (defaultDefn defaultArgInfo aux withFunType emptyFunction)
                   { defDisplay = [df] }
  -- solveSizeConstraints -- Andreas, 2012-10-16 does not seem necessary

  reportSDoc "tc.with.top" 10 $ sep
    [ text "added with function" <+> (prettyTCM aux) <+> text "of type"
    , nest 2 $ prettyTCM withFunType
    , nest 2 $ text "-|" <+> (prettyTCM =<< getContextTelescope)
    ]

  -- Construct the body for the with function
  cs <- return $ map (A.lhsToSpine) cs
  cs <- buildWithFunction cxtNames f aux t qs npars withSub finalPerm (size delta1) n cs
  cs <- return $ map (A.spineToLhs) cs

  -- Check the with function
  checkFunDefS withFunType defaultArgInfo NotDelayed Nothing (Just f) info aux (Just withSub) cs

  where
    info = Info.mkDefInfo (nameConcrete $ qnameName aux) noFixity' PublicAccess ConcreteDef (getRange cs)

-- | Type check a where clause.
checkWhere
  :: Type            -- ^ Type of rhs.
  -> [A.Declaration] -- ^ Where-declarations to check.
  -> TCM a           -- ^ Continuation.
  -> TCM a
checkWhere trhs ds ret = do
  let
    loop ds = case ds of
      [] -> ret
      [A.ScopedDecl scope ds] -> withScope_ scope $ loop ds
      [A.Section _ m tel ds]  -> do
        checkTelescope tel $ \ tel' -> do
          reportSDoc "tc.def.where" 10 $
            text "adding section:" <+> prettyTCM m <+> text (show (size tel'))
          addSection m
          verboseS "tc.def.where" 10 $ do
            dx   <- prettyTCM m
            dtel <- mapM prettyAs tel
            dtel' <- prettyTCM =<< lookupSection m
            reportSLn "tc.def.where" 10 $ "checking where section " ++ show dx ++ " " ++ show dtel
            reportSLn "tc.def.where" 10 $ "        actual tele: " ++ show dtel'
          withCurrentModule m $ local (\ e -> e { envCheckingWhere = True }) $ do
            checkDecls ds
            ret
      _ -> __IMPOSSIBLE__
  loop ds

-- | Check if a pattern contains an absurd pattern. For instance, @suc ()@
containsAbsurdPattern :: A.Pattern -> Bool
containsAbsurdPattern p = case p of
    A.AbsurdP _   -> True
    A.VarP _      -> False
    A.WildP _     -> False
    A.DotP _ _    -> False
    A.LitP _      -> False
    A.AsP _ _ p   -> containsAbsurdPattern p
    A.ConP _ _ ps -> any (containsAbsurdPattern . namedArg) ps
    A.RecP _ fs   -> any (containsAbsurdPattern . (^. exprFieldA)) fs
    A.ProjP _ _   -> False
    A.DefP _ _ ps -> any (containsAbsurdPattern . namedArg) ps
    A.PatternSynP _ _ _ -> __IMPOSSIBLE__ -- False

-- | Set the current clause number.
atClause :: QName -> Int -> TCM a -> TCM a
atClause name i = local $ \ e -> e { envClause = IPClause name i }
