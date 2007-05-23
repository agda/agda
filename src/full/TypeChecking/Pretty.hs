{-# OPTIONS_GHC -fglasgow-exts -fallow-undecidable-instances #-}

module TypeChecking.Pretty where

import Control.Applicative hiding (empty)

import Syntax.Common
import Syntax.Internal
import Syntax.Translation.InternalToAbstract
import Syntax.Translation.AbstractToConcrete
import qualified Syntax.Abstract as A
import qualified Syntax.Abstract.Pretty as P
import qualified Syntax.Concrete.Pretty as P

import TypeChecking.Monad

import qualified Utils.Pretty as P
import Utils.Pretty (Doc)

---------------------------------------------------------------------------
-- * Wrappers for pretty printing combinators
---------------------------------------------------------------------------

empty, comma :: MonadTCM tcm => tcm Doc

empty	   = return P.empty
comma	   = return P.comma
pretty x   = return $ P.pretty x
prettyA x  = P.prettyA x
text s	   = return $ P.text s
pwords s   = map return $ P.pwords s
fwords s   = return $ P.fwords s
sep ds	   = P.sep <$> sequence ds
fsep ds    = P.fsep <$> sequence ds
hsep ds    = P.hsep <$> sequence ds
vcat ds    = P.vcat <$> sequence ds
d1 $$ d2   = (P.$$) <$> d1 <*> d2
d1 <> d2   = (P.<>) <$> d1 <*> d2
d1 <+> d2  = (P.<+>) <$> d1 <*> d2
nest n d   = P.nest n <$> d
braces d   = P.braces <$> d
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

instance PrettyTCM Term where prettyTCM x = prettyA =<< reify x
instance PrettyTCM Type where prettyTCM x = prettyA =<< reify x
instance PrettyTCM Sort where prettyTCM x = prettyA =<< reify x

instance (Reify a e, ToConcrete e c, P.Pretty c) => PrettyTCM (Arg a) where
    prettyTCM x = prettyA =<< reify x

instance PrettyTCM A.Expr where
    prettyTCM = prettyA

instance PrettyTCM Constraint where
    prettyTCM c = case c of
	ValueEq ty s t ->
	    sep [ sep [ prettyTCM s
		      , text "==" <+> prettyTCM t
		      ]
		, nest 2 $ text ":" <+> prettyTCM ty
		]
	TypeEq a b ->
	    sep [ prettyTCM a
		, text "==" <+> prettyTCM b
		]
	SortEq s1 s2 ->
	    sep [ prettyTCM s1
		, text "==" <+> prettyTCM s2
		]
	Guarded c cs ->
	    sep [ prettyTCM c
		, nest 2 $ brackets $ sep $ punctuate comma $ map prettyTCM cs
		]
	UnBlock m   -> do
	    BlockedConst t <- mvInstantiation <$> lookupMeta m
	    sep [ text (show m) <+> text ":="
		, nest 2 $ prettyTCM t
		]


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

instance PrettyTCM Context where
    prettyTCM ctx = P.fsep . reverse <$> pr ctx
	where
	    pr []		   = return []
	    pr (Arg h (x,t) : ctx) = escapeContext 1 $ do
		d    <- prettyTCM t
		x    <- prettyTCM x
		dctx <- pr ctx
		return $ par h (P.hsep [ x, P.text ":", d]) : dctx
	      where
		par NotHidden = P.parens
		par Hidden    = P.braces

