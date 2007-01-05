
%include lhs2TeX.fmt

%if anyMath

%format .     = ".~"
%format alpha = "\alpha"
%format beta  = "\beta"
%format gamma = "\gamma"
%format delta = "\delta"
%format phi   = "\phi"
%format psi   = "\psi"
%format Set   = "\SET"
%format |-    = "\vdash"
%format ?     = "~{?}"

%format when  = "\mathbf{when}"

%endif


%However, when adding meta-variables things get more complicated.
%The convertibility of $A$ and $B$ might now be unknown until some of the meta
%variables have been instantiated.We will give an example illustrating the problem. Given 
%the set of natural numbers, |Nat|, and the set of booleans, |Bool|. Given also a function, |F : Bool -> Set|. The problem we consider is checking if the term 
%|\g. g 0| has type|((x : F ?) -> F (not x)) -> Nat|
%, where the term |?| is a meta-variable of type |Bool| and |0| is a natural number. We now get the constraints |F ? = Bool|, |F ? = Nat|,
% and |F (not 0) = Nat|. We can now see that we have a problem since |F (not 0)|
% is ill-typed. 


When adding meta-variables equality checking gets more complicated, since we cannot
always decide the validity of an equality, and we may be forced to keep it as a
constraint. This is well-known in higher order
unification\cite{huet:unification}: the constraint $?~0 = 0$ has two solutions
$? = \lambda x.x$ and $? = \lambda x.0$. This appears also in type theory with
constraints of the form |F ? = Bool| where $F$ is defined by computation rules.
The fact that we type check modulo yet unsolved constraints can lead to
ill-typed terms.
For instance, 
consider the type-checking problem
|\g. g 0:((x : F ?) -> F (not x)) -> Nat|\footnote{The notation |(x:A) -> B x| should be read as $\forall x:A. B ~x$.}
where the term ? is a meta-variable of type |Bool|, |0:Nat|, and |F:Bool->Set| where |F false = Nat| and |F true = Bool|.
First we check that |((x : F ?) -> F (not x)) -> Nat| is a well-formed type, which
generates the constraint |F ? = Bool|, since the term |not x| forces |x| to be
of type |Bool|. Checking |\g.g 0| against the type |((x : F ?) -> F (not x)) -> Nat|
generate then the constraints |F ? = Nat| and then |F (not 0) = Nat|, which contains
an ill-typed term\footnote{In fact we will also get the constraint |Bool = Bool| which is trivially 
valid and therefore left out.}. 

