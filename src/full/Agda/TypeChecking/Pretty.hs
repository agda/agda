{-# LANGUAGE CPP, TypeSynonymInstances, FlexibleInstances,
             UndecidableInstances #-}
module Agda.TypeChecking.Pretty where

import Control.Applicative hiding (empty)

import Agda.Syntax.Common
import Agda.Syntax.Internal
import Agda.Syntax.Literal
import Agda.Syntax.Translation.InternalToAbstract
import Agda.Syntax.Translation.AbstractToConcrete
import qualified Agda.Syntax.Abstract as A
import qualified Agda.Syntax.Abstract.Pretty as P
import qualified Agda.Syntax.Concrete.Pretty as P

import Agda.TypeChecking.Monad

import qualified Agda.Utils.Pretty as P
import Agda.Utils.Impossible

#include "../undefined.h"

---------------------------------------------------------------------------
-- * Wrappers for pretty printing combinators
---------------------------------------------------------------------------

type Doc = P.Doc

empty, comma :: MonadTCM tcm => tcm Doc

empty	   = return P.empty
comma	   = return P.comma
pretty x   = return $ P.pretty x
prettyA x  = P.prettyA x
text :: MonadTCM tcm => String -> tcm Doc
text s	   = return $ P.text s
pwords s   = map return $ P.pwords s
fwords s   = return $ P.fwords s
sep, fsep, hsep, vcat :: MonadTCM tcm => [tcm Doc] -> tcm Doc
sep ds	   = P.sep <$> sequence ds
fsep ds    = P.fsep <$> sequence ds
hsep ds    = P.hsep <$> sequence ds
vcat ds    = P.vcat <$> sequence ds
($$), (<>), (<+>) :: MonadTCM tcm => tcm Doc -> tcm Doc -> tcm Doc
d1 $$ d2   = (P.$$) <$> d1 <*> d2
d1 <> d2   = (P.<>) <$> d1 <*> d2
d1 <+> d2  = (P.<+>) <$> d1 <*> d2
nest n d   = P.nest n <$> d
braces d   = P.braces <$> d
dbraces d  = P.dbraces <$> d
brackets d = P.brackets <$> d
parens d   = P.parens <$> d

prettyList ds = brackets $ fsep $ punctuate comma ds

punctuate _ [] = []
punctuate d ds = zipWith (<>) ds (replicate n d ++ [empty])
    where
	n = length ds - 1

---------------------------------------------------------------------------
-- * The PrettyTCM class
---------------------------------------------------------------------------

class PrettyTCM a where
    prettyTCM :: MonadTCM tcm => a -> tcm Doc

instance PrettyTCM a => PrettyTCM (Closure a) where
    prettyTCM cl = enterClosure cl prettyTCM

instance PrettyTCM a => PrettyTCM [a] where
  prettyTCM = prettyList . map prettyTCM

instance PrettyTCM Term where prettyTCM x = prettyA =<< reify x
instance PrettyTCM Type where prettyTCM x = prettyA =<< reify x
instance PrettyTCM Sort where prettyTCM x = prettyA =<< reify x
instance PrettyTCM DisplayTerm where prettyTCM x = prettyA =<< reify x
instance PrettyTCM NamedClause where prettyTCM x = prettyA =<< reify x
instance PrettyTCM Level where prettyTCM x = prettyA =<< reify (Level x)

instance PrettyTCM ClauseBody where
  prettyTCM b = do
    (binds, body) <- walk b
    sep [ brackets (fsep binds), return body ]
    where
      walk NoBody = return ([], P.text "()")
      walk (Body v) = (,) [] <$> prettyTCM v
      walk (NoBind b) = do
        (bs, v) <- walk b
        return (text "." : bs, v)
      walk (Bind b) = do
        (bs, v) <- underAbstraction_ b walk
        return (text (absName b) : bs, v)

instance (PrettyTCM a, PrettyTCM b) => PrettyTCM (Judgement a b) where
  prettyTCM (HasType a t) = prettyTCM a <+> text ":" <+> prettyTCM t
  prettyTCM (IsSort  a t) = text "Sort" <+> prettyTCM a <+> text ":" <+> prettyTCM t

instance PrettyTCM MetaId where
  prettyTCM = text . show

instance PrettyTCM a => PrettyTCM (Blocked a) where
  prettyTCM (Blocked x a) = text "[" <+> prettyTCM a <+> text "]" <> text (show x)
  prettyTCM (NotBlocked x) = prettyTCM x

instance (Reify a e, ToConcrete e c, P.Pretty c) => PrettyTCM (Arg a) where
    prettyTCM x = prettyA =<< reify x

instance PrettyTCM A.Expr where
    prettyTCM = prettyA

instance PrettyTCM Relevance where
  prettyTCM Irrelevant = text "."
  prettyTCM NonStrict  = text ".."
  prettyTCM Relevant   = empty
  prettyTCM Forced     = empty

instance PrettyTCM Comparison where
  prettyTCM CmpEq  = text "=="
  prettyTCM CmpLeq = text "=<"

instance PrettyTCM Constraint where
    prettyTCM c = case c of
	ValueCmp cmp ty s t ->
	    sep [ sep [ prettyTCM s
		      , prettyTCM cmp <+> prettyTCM t
		      ]
		, nest 2 $ text ":" <+> prettyTCM ty
		]
        ArgsCmp cmps t us vs ->
          sep [ prettyList
                [ sep [ prettyTCM u
                      , nest 2 $ text "~~" <+> prettyTCM v
                      , nest 2 $ text (show cmp)
                      ] | (cmp, u, v) <- zip3 (cmps ++ repeat Invariant) us vs
                ]
              , nest 2 $ text ":" <+> prettyTCM t
              ]
	LevelCmp cmp a b ->
	    sep [ prettyTCM a
		, prettyTCM cmp <+> prettyTCM b
		]
	TypeCmp cmp a b ->
	    sep [ prettyTCM a
		, prettyTCM cmp <+> prettyTCM b
		]
	TelCmp a b cmp tela telb ->
	    sep [ prettyTCM tela
		, prettyTCM cmp <+> prettyTCM telb
		]
	SortCmp cmp s1 s2 ->
	    sep [ prettyTCM s1
		, prettyTCM cmp <+> prettyTCM s2
		]
	Guarded c cs ->
	    sep [ prettyTCM c
		, nest 2 $ brackets $ sep $ punctuate comma $ map prettyTCM cs
		]
	UnBlock m   -> do
	    -- BlockedConst t <- mvInstantiation <$> lookupMeta m
	    mi <- mvInstantiation <$> lookupMeta m
            case mi of
              BlockedConst t ->
                sep [ text (show m) <+> text ":="
                    , nest 2 $ prettyTCM t
                    ]
              PostponedTypeCheckingProblem cl -> enterClosure cl $ \(e, a, _) ->
                sep [ text (show m) <+> text ":="
                    , nest 2 $ sep [ prettyA e <+> text ":?"
                                   , prettyTCM a
                                   ]
                    ]
              Open{}  -> __IMPOSSIBLE__
              OpenIFS{}  -> __IMPOSSIBLE__
              InstS{} -> __IMPOSSIBLE__
              InstV{} -> __IMPOSSIBLE__
	FindInScope m   -> sep [ text $ "Find in scope " ++ (show m) ]
        IsEmpty t ->
            sep [ text "Is empty:", nest 2 $ prettyTCM t ]

instance PrettyTCM Literal where
  prettyTCM = text . show

instance PrettyTCM Name where
    prettyTCM x = P.pretty <$> abstractToConcrete_ x

instance PrettyTCM QName where
    prettyTCM x = P.pretty <$> abstractToConcrete_ x

instance PrettyTCM ModuleName where
  prettyTCM x = P.pretty <$> abstractToConcrete_ x

instance PrettyTCM Telescope where
  prettyTCM tel = P.fsep . map P.pretty <$> (do
      tel <- reify tel
      runAbsToCon $ bindToConcrete tel return
    )

newtype PrettyContext = PrettyContext Context

instance PrettyTCM PrettyContext where
  prettyTCM (PrettyContext ctx) = P.fsep . reverse <$> pr (map ctxEntry ctx)
      where
          pr []		   = return []
          pr (Arg h r (x,t) : ctx) = escapeContext 1 $ do
              d    <- prettyTCM t
              x    <- prettyTCM x
              dctx <- pr ctx
              return $ P.pRelevance r (par h (P.hsep [ x, P.text ":", d])) : dctx
            where
              par NotHidden = P.parens
              par Hidden    = P.braces
              par Instance  = P.dbraces

instance PrettyTCM Context where
  prettyTCM = prettyTCM . PrettyContext
