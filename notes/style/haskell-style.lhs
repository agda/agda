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

Provide haddock comments to at least

\begin{itemize}
\item top-level functions,
\item type and data type declarations,
\item each constructor of a data type,
\item each field of a record.
\end{itemize}

TODO: examples.

Agda TODO: add missing haddock comments.

\subsection{Indentation}

Uniformly indent your code.  There are two evils:
\begin{itemize}
\item Too little indentation:  This makes it too hard for the human
  reader to see the structure.  \textbf{1 space identation is too
    little!}
\item Too much indentation.  You might not care if you have a 27 inch
  display and a line length of 256 characters.  However, we care!  A
  line should usually fit within 80-100 characters.
\end{itemize}
Recommended indentation is \emph{2 characters}. Upto 4 characters are
tolerated.

\subsubsection{Indenting |data|}

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


\end{document}
