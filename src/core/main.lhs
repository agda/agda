\documentclass{article} 
%include polycode.fmt 
%include lhs2TeX.fmt
%%include polytt.fmt
%%subst code a = "\begin{colorcode}\thinmuskip=10mu\medmuskip=10mu\thickmuskip=10mu\relax'n" a "\end{colorcode}\resethooks'n" 
\input{ttinit}
\input{ttinitmore}
\newcommand{\Val}{\mathbf{Val}}
\newcommand{\Set}{\mathbf{Set}}
\newcommand{\Fun}{\mathbf{Fun}}
\newcommand{\App}{\mathbf{App}}
\begin{document}
\include{overview} 
%include Decl.lhs
%include Check.lhs
%include Exp.lhs
%include Val.lhs
%include Conv.lhs
%include Cont.lhs
\end{document}