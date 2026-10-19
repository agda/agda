module Agda.TypeChecking.Rewriting.Errors (prettyIllegal) where

import Agda.TypeChecking.Monad.Base
import Agda.TypeChecking.Monad.Constraints
import Agda.TypeChecking.Monad.Context ( addContext )
import Agda.TypeChecking.Pretty

import Agda.Syntax.Common.Pretty ( Pretty, prettyShow, singPlural )
import Agda.Syntax.Internal

import Agda.Interaction.Options.Warnings

import qualified Agda.Utils.Set1 as Set1
import qualified Agda.Utils.VarSet as VarSet

{-# SPECIALIZE prettyIllegal :: SerialisableRewriteOrigin -> IllegalRewriteRuleReason -> TCM Doc #-}
prettyIllegal ::
     MonadPretty m
  => SerialisableRewriteOrigin -> IllegalRewriteRuleReason -> m Doc
prettyIllegal q reason = do
  let illegalSince q = [ prettyTCM q, "" ] ++
              pwords "is not a legal" ++
              (if isSmartWithRewrite q then pwords "(--smart-with)" else []) ++
              pwords "rewrite rule, since"
  case reason of

    LHSNotDefinitionOrConstructor -> do
      (fsep . concat)
        [ illegalSince q
        , pwords "the left-hand side is neither a defined symbol nor a constructor"
        ]

    LHSNotNeutral r -> do
      (fsep . concat)
        [ illegalSince q
        , pwords "the left-hand side is"
        , case r of
            LHSConstructorHeaded -> pwords
              "headed by a constructor"
            LHSUnderapplied      -> pwords
              "underapplied"]

    RHSContainsClosures -> do
      (fsep . concat)
        [ illegalSince q
        , pwords "the right-hand side contains closures (lambdas or underapplied functions)"]

    IntervalVariablesPresent xs -> do
      (fsep . concat)
        [ illegalSince q
        , pwords "the following interval"
        , pwords $ singPlural ys "variable is" "variables are"
        , pwords "present:" ]
        <?> fsep (map (prettyTCM . var) ys)
      where ys = VarSet.toAscList xs

    VariablesNotBoundByLHS xs -> do
      (fsep . concat)
        [ illegalSince q
        , pwords "the following"
        , pwords $ singPlural ys "variable is" "variables are"
        , pwords "not bound by the left hand side:"
        ]
      <?> fsep (map (prettyTCM . var) ys)
      where ys = VarSet.toAscList xs

    VariablesBoundMoreThanOnce xs -> do
      (fsep . concat)
        [ illegalSince q
        , pwords "the following"
        , pwords $ singPlural ys "parameter is" "parameters are"
        , pwords "bound more than once on the left hand side:"
        ]
      <?> fsep (map (prettyTCM . var) ys)
      $$ fwords "(Perhaps you can use a postulate instead of a constructor as the head symbol?)"
      where ys = VarSet.toAscList xs

    VariablesBoundInSingleton xs -> do
      -- This warning is motivated in #8238. If #6636 is implemented, then
      -- this warning should be disabled.
      (fsep . concat)
        [ pwords "I am not certain that the rewrite rule"
        , [ "", prettyTCM q, "" ]
        , pwords "is safe because it appears that the following"
        , pwords $ singPlural ys "variable is" "variables are"
        , pwords "only bound in contexts which might become definitionally singular:"
        ]
      <?> fsep (map (prettyTCM . var) ys)
      $$ fwords "This warning can be silenced with"
      <?> hcat [ "-Wno", text (warningNameToString RewriteVariablesBoundInSingleton_) ]
      $$ fwords "but be aware that this rewrite might behave strangely in the presence of e.g. eta records with no fields"
      where ys = VarSet.toAscList xs

    LHSReduces v v' -> vcat
      [ (fsep . concat) [ illegalSince q, pwords "the left-hand side" ]
      , nest 2 $ prettyTCM v
      , fwords "reduces to"
      , nest 2 $ prettyTCM v'
      ]

    HeadSymbolIsProjectionLikeFunction f -> vcat
      [ (fsep . concat)
        [ illegalSince q , pwords "the head symbol"
        , [ "", hd, ""]
        , pwords "is a projection-like function."
        ]
      , (fsep . concat)
        [ pwords "You can turn off the projection-like optimization for"
        , [ hd ]
        , pwords "with the pragma"
        ]
      , nest 2 $ fsep [ "{-# NOT_PROJECTION_LIKE", hd, "#-}" ]
      , fwords "or globally with the flag --no-projection-like"
      ]
      where hd = prettyTCM f

    HeadSymbolIsTypeConstructor f -> (fsep . concat)
      [ illegalSince q
      , pwords "the head symbol"
      , [ prettyTCM f ]
      , pwords "is a type constructor."
      ]

    HeadSymbolContainsMetas f -> (fsep . concat)
      [ illegalSince q
      , pwords "the definition of the head symbol"
      , [ prettyTCM f ]
      , pwords "contains unsolved metavariables and confluence checking is enabled."
      ]

    ConstructorParametersNotGeneral c vs -> vcat
      [ (fsep . concat) [ illegalSince q, pwords "the constructor parameters are not fully general:" ]
      , nest 2 $ text "Constructor: " <+> prettyTCM c
      , nest 2 $ (pluralS vs "Parameter" <> ": ") <+> fsep (punctuate ";" $ fmap prettyTCM vs)
      ]

    ContainsUnsolvedMetaVariables ms -> do
      (fsep . concat)
        [ illegalSince q
        , pwords "it contains the unsolved meta"
        , [ pluralS ms "variable" <> colon ]
        ]
      <?> fsep (fmap prettyTCM $ Set1.toList ms)

    BlockedOnProblems ps -> do
      (fsep . concat)
        [ illegalSince q
        , pwords "it is blocked on"
        , [ pluralS ps "problem" <> colon]
        ]
      <?> fsep (fmap prettyTCM $ Set1.toList ps)

    RequiresDefinitions qs -> do
      (fsep . concat)
        [ illegalSince q
        , pwords "it requires the"
        , [ pluralS qs "definition", "of" <> colon]
        ]
      <?> fsep (fmap prettyTCM $ Set1.toList qs)

    DoesNotTargetRewriteRelation -> (fsep . concat)
      [ [ prettyTCM q, "" ], pwords "does not target rewrite relation" ]

    BeforeFunctionDefinition -> (fsep . concat)
      [ pwords "Rewrite rule from function"
      , [ "", prettyTCM q, ""]
      , pwords "cannot be added before the function definition"
      ]

    BeforeMutualFunctionDefinition r -> (fsep . concat)
      [ pwords "Rewrite rule from function"
      , [ "", prettyTCM q, ""]
      , pwords "cannot be added before the definition of mutually defined"
      , [ prettyTCM r ]
      ]

    DuplicateRewriteRule -> (fsep . concat)
      [ pwords "Rewrite rule"
      , [ "", prettyTCM q, ""]
      , pwords "has already been added"
      ]

    LocalRewriteOutsideTelescope -> (fsep . concat)
      [ illegalSince q
      , pwords "local rewrite rules are (currently) only allowed in module telescopes. Consider creating an anonymous module"
      ]

    SmartWithOccursFail -> (fsep . concat)
      [ illegalSince q
      , pwords "the left-hand side occurs somewhere in an earlier '--smart-with' rewrite rule"
      ]

instance PrettyTCM SerialisableRewriteOrigin where
  prettyTCM = \case
    LocalRewrite (LocalRewriteInfo o g n t) ->
      maybe "_" prettyTCM n <+> ":" <+> addContext g (prettyTCM t)
    GlobalRewrite q -> prettyTCM q

instance PrettyTCM RewriteOrigin where
  prettyTCM s = prettyTCM (defName <$> s)
