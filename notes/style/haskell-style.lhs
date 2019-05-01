\nonstopmode
\documentclass[14pt]{scrartcl} % KOMA-Script article

%include polycode.fmt
%% %format . = "."

\usepackage{hyperref}

\title{Agda's Style Guide to Haskell Programming}
\author{Andreas Abel}
\date{December 2013}

\newcommand{\hidden}[1]{}

\begin{document}
\maketitle

\section{Introduction}

Agda style!

This is a style guide to Haskell programming.  It more or less
reflects the predominant style in the source code of Agda.  Try to
adhere to it if you contribute to Agda!  Agda is going be around for
much longer (hopefully), so the code base must be readable and
maintainable.

\section{Mandatory style}

\subsection{Type signatures}

Besides their role in type checking and error location, type
signatures are an always up-to-date rudimentary documentation of a
function.

Each top-level function must come with a type signature.  If you are
too lazy to write it yourself, let ghci figure it out for you and
paste it in.  It might be too general so specalize it appropriately if
necessary.

\subsection{Haddock comments}

Provide Haddock comments to at least

\begin{itemize}
\item top-level functions,
\item type and data type declarations,
\item each constructor of a data type,
\item each field of a record.
\end{itemize}

TODO: examples.

Agda TODO: add missing Haddock comments.

\subsection{Indentation}

Uniformly indent your code.  There are two evils:
\begin{itemize}
\item Too little indentation:  This makes it too hard for the human
  reader to see the structure.  \textbf{1 space indentation is too
    little!}
\item Too much indentation.  You might not care if you have a 27 inch
  display and a line length of 256 characters.  However, we care!  A
  line should usually fit within 80-100 characters.
\end{itemize}
Recommended indentation is \emph{2 characters}. Upto 4 characters are
tolerated.

\subsubsection{Indenting and haddocking |data|}

Bad:
\begin{code}
  data MyDataType =  MyConstructor1
                  |  MyConstructor2
                  |  MyConstructor3
                     deriving (Typable, Show)
\end{code}
Good:
\begin{code}
  -- | @MyDataType@ is awesome!
  data MyDataType
    =  MyConstructor1  -- ^ Cool thing.
    |  MyConstructor2  -- ^ Great stuff.
    |  MyConstructor3  -- ^ Terrific, or?
    deriving (Typable, Show)
\end{code}
Also good:
\begin{code}
  -- | @MyDataType@ is awesome!
  data MyDataType
      =  MyConstructor1
         -- ^ Cool thing.
      |  MyConstructor2
         -- ^ Great stuff.
      |  MyConstructor3
         -- ^ Terrific.
    deriving (Typable, Show)
\end{code}


\begin{code}
\end{code}
\hidden{
\begin{code}
\end{code}
}

\section{Module structure}

A module consists of the following parts, in the following order:
\begin{itemize}
\item GHC language extensions, one per line, in alphabetical
  order.  Use only language extensions supported by GHC 6.12 and
  later.
\item A haddock module comment.
\item The module, possibly with export list.
\item Imports.  First the external imports, then the \verb+Agda.*+
  modules.
  \begin{itemize}
  \item |Data.Map| is imported qualified as |Map|, |Data.Set| as
    |Set|.
  \item The qualifiers for Agda modules are, if used:
     |A| for |Agda.Syntax.Abstract|,
     |C| for |Agda.Syntax.Concrete|,
     |Common| for |Agda.Syntax.Common|,
     |I| for |Agda.Syntax.Internal|,
     |TCM| for |Agda.TypeChecking.Monad|.
  \end{itemize}
\end{itemize}


\begin{code}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TupleSections     #-}

-- | A longer comment explaining this modules intention.
--
--   This module intents to explain the Agda module structure.
--   Bla bla...

module Agda.Module.Structure where

import Control.Monad.Error
import Control.Monad.State
import Control.Bla

import Data.Function
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Bla

import Agda.Interaction.Bla

import Agda.Syntax.Abstract as A
import Agda.Syntax.Common as Common
import Agda.Syntax.Concrete as C
import Agda.Syntax.Internal as I
import Agda.Syntax.Bla

import Agda.TypeChecking.Monad as TCM
import Agda.TypeChecking.Monad.Bla
import Agda.TypeChecking.Positivity
import Agda.TypeChecking.Bla

import Agda.Termination.Bla

import Agda.Utils.Maybe
import Agda.Utils.Bla

import Agda.Utils.Impossible

---------------------------------------------------------------------------
-- * Group 1
---------------------------------------------------------------------------

... definitions ...

---------------------------------------------------------------------------
-- * Group 2
---------------------------------------------------------------------------

... definitions ...

...

\end{code}



\end{document}
