\documentclass{article}
\usepackage{hyperref}
\usepackage[links]{agda}
\begin{document}

\AgdaTarget{ℕ}
\AgdaTarget{zero}
\begin{code}
data ℕ : Set where
  zero  : ℕ
  suc   : ℕ → ℕ
\end{code}

See next page for how to define \AgdaFunction{two} (doesn't turn into a
link because the target hasn't been defined yet). We could do it
manually though; \hyperlink{two}{\AgdaDatatype{two}}.

\newpage

\AgdaTarget{two}
\hypertarget{two}{}
\begin{code}
two : ℕ
two = suc (suc zero)
\end{code}

\AgdaInductiveConstructor{zero} is of type
\AgdaDatatype{ℕ}. \AgdaInductiveConstructor{suc} has not been defined to
be a target so it doesn't turn into a link.

\newpage

Now that the target for \AgdaFunction{two} has been defined the link
works automatically.

\begin{code}
data Bool : Set where
  true false : Bool
\end{code}

The AgdaTarget command takes a list as input, enabling several targets
to be specified as follows:

\AgdaTarget{if, then, else, if\_then\_else\_}
\begin{code}
if_then_else_ : {A : Set} → Bool → A → A → A
if true then t else f = t
if false then t else f = f
\end{code}

\newpage

Mixfix identifier need their underscores escaped:
\AgdaFunction{if\_then\_else\_}.

\end{document}
