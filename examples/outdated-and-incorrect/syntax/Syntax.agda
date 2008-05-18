
{-  An agda file contains a single module. The module name should correspond to
    the name and path of the file. The path is relative to the project root. In
    this case the project root is the root of Agda II. Modules can be
    parameterised, but in this case we choose not to parameterise the top-level
    module.
-}

module examples.syntax.Syntax where

  -- It is recommended that the body of the top-level module is indented by a
  -- small amount, but this is not enforced in the syntax.

  -- You can have modules inside modules. The name of a sub-module isn't
  -- qualified.
  module Expressions (X : Set)(x1, x2 : X) where

    -- There are three forms of sorts. Set = Set0.
    postulate A1 : Set
	      A2 : Set3
	      A3 : Prop

    -- Independent function space.
    fun1 : X -> X
    fun1 x = x

    -- Implicit independent function space. This is mostly included for
    -- symmetry, I can't come up with an example when this would be useful.
    fun2 : {X} -> X
    fun2 {x} = x

    -- Dependent function space.
    fun3 : (A:Set) -> A -> A
    fun3 A x = x

    -- Implicit dependent function space. 'A' is implicit so we don't have to
    -- write it out in the function definition.
    fun4 : {A:Set} -> A -> A
    fun4 x = x

    -- You can also write independent functions using the dependent function
    -- space syntax. Not that you'd ever want to.
    fun5 : (_:X) -> X
    fun5 x = x

    -- Lambdas can be domain free.
    const1 : {A, B : Set} -> A -> B -> A
    const1 = \x y -> x

    -- Or completely typed.
    const2 = \{A:Set}{B:Set}(x:A)(y:B) -> x -- inferable, no type needed

    -- You cannot mix typed and untyped arguments in the same lambda.
    const3 : {A, B : Set} -> A -> B -> A
    const3 = \{A}{B} -> \(x:A)(y:B) -> x

    -- You can have wildcards in lambdas
    const4 : {A, B : Set} -> A -> B -> A
    const4 = \x _ -> x

    -- Implicit arguments can be omitted in applications.
    x = const1 x1 x2

    -- Or made explicit.
    x' = const1 {X} {X} x1 x2

    -- Infix operators can be bound by lambdas. See ComplexDeclarations for
    -- more information about infix operators.
    dup : {A:Set} -> (A -> A -> A) -> A -> A
    dup = \(+) x -> x + x

  -- The two basic declarations are function definitions and datatype
  -- declarations.
  module BasicDeclarations (X : Set) where

    -- The most common declaration is the function definition. It consists of
    -- two parts; a type signature and a set of function clauses. Type
    -- signatures have the form 'id : type', no telescopes are allowed at this
    -- point. This can be discussed.
    id : X -> X
    id x = x

    -- You can omit the type signature if the type can be inferred.
    id' = id

    -- Datatypes are introduced with the data keyword.
    data Bool : Set where
      false : Bool
      true  : Bool

    -- The parameters to the datatype (A in this case) are in scope in the
    -- types of the constructors. At the moment inductive families are not
    -- supported.
    data List (A : Set) : Set where
      nil  : List A
      (::) : A -> List A -> List A

    -- When using a constructor as a function, the parameters are hidden
    -- arguments.
    singleton : X -> List X
    singleton x = x :: nil

    singleton' : X -> List X
    singleton' x = (::) {X} x (nil {X})

    -- You can pattern match over elements of a datatype when defining
    -- functions (and only then).
    null : (A : Set) -> List A -> Bool
    null A nil	   = true
    null A (x::xs) = false

    -- Patterns can be nested (and functions can be recursive).
    and : List Bool -> Bool
    and nil	    = true
    and (true::xs)  = and xs
    and (false::xs) = false

    -- Functions can be defined in an infix style. When doing this it must be
    -- clear what name is being defined without looking at fixities. Hence we
    -- could never remove the parenthesis around x::xs in the second clause.
    (++) : List X -> List X -> List X
    nil	    ++ ys = ys
    (x::xs) ++ ys = x :: (xs ++ ys)

    -- You can also use a combination of infix and prefix.
    (@) : {A, B, C : Set} -> (B -> C) -> (A -> B) -> A -> C
    (f @ g) x = f (g x)

  -- Declarations can appear in many different contexts and not all
  -- declarations are allowed everywhere.
  module ComplexDeclarations (X : Set) where

    -- You can introduce new constants with the postulate declaration. A
    -- postulate declaration takes a list of type signatures.
    postulate A : Set
	      a : A

    -- Let's introduce some datatypes so we have something to work with. At the
    -- same time we illustrate that layout is optional.
    data Nat  : Set where { zero : Nat;   suc  : Nat -> Nat }
    data Bool : Set where { false : Bool; true : Bool }

    {- We can declare the fixity of infix symbols. The fixity is tied to a
       particular binding of a name. The binding doesn't have to be in scope
       directly (as in the example below), but it should be possible to bring
       it into scope by moving the fixity declaration further down in the
       current block (but never inside things).

       The following wouldn't be allowed:

         infixl 15 +
         mutual
	   (+) : Nat -> Nat -> Nat
	   ..

       There are three forms: infix, infixl and infixr, for non-associative,
       left associative and right associative respectively. The number is the
       precedence level.
    -}

    infixl 15 +, `plus`

    (+) : Nat -> Nat -> Nat
    n + zero  = zero
    n + suc m = suc (n + m)

    plus = (+)

    -- The following code is to stress test the handling of infix applications.

    infixl 10 @
    infixl 11 @@
    infixr 10 #
    infixr 11 ##
    postulate
      (@)  : Nat -> Nat -> Nat
      (#)  : Nat -> Nat -> Nat
      (@@) : Nat -> Nat -> Nat
      (##) : Nat -> Nat -> Nat

    z = zero

    test1 = z @ (z # z)
    test2 = (z @ z) # z
    test3 = z # (z @ z)
    test4 = (z # z) @ z
    test5 = z ## z # z ## z # z
    test6 = z @@ z @ z @@ z @ z
    test7 = z # z @@ z @@ z # z

    -- Mutually recursive definition are introduced using the 'mutual' keyword.
    -- A mutual block can contain function definitions, datatypes
    -- (induction-recursion) and fixity declarations.
    mutual
      even : Nat -> Bool
      even zero	    = true
      even (suc n)  = odd n

      odd : Nat -> Bool
      odd zero	    = false
      odd (suc n)   = even n

    -- If a function is declared abstract the definition of the function is not
    -- visible outside the module. For an abstract datatype the constructors
    -- are hidden. Definitions that can appear in an abstract block are:
    -- function definitions, data declarations, fixity declarations, mutual
    -- blocks, open and name space declarations (see NameSpaces).
    abstract
      data Stack : Set where
	nil  : Stack
	cons : A -> Stack -> Stack

      empty : Stack
      empty = nil

      push : A -> Stack -> Stack
      push = cons

    -- Local declarations are introduces either with a let or in a where
    -- clause. A where clause is attached to a function clause. Everything that
    -- can appear in an abstract block can appear in a local declaration, plus
    -- abstract blocks. Local functions can be recursive.
    foo : (A : Set) -> A -> A
    foo A x = let f : Local -> A
		  f (local y) = y
	      in  f (local x)
      where
	data Local : Set where
	  local : A -> Local

    -- You can declare things to be private to the current module. This means
    -- that they cannot be accessed outside the module (but they're still
    -- visible inside the module and its submodules). The only things that
    -- cannot appear in a private block are other private blocks and import
    -- statements.
    private
      bar : X -> X
      bar x = x

    -- Private declarations can go inside mutual and abstract blocks.
    mutual
      private f : Nat -> Nat
	      f zero	= zero
	      f (suc n) = g n

      g : Nat -> Nat
      g n = f n

    abstract
      Nat' : Set
      Nat' = Nat

      private h : Nat' -> Nat
	      h n = n


  -- A name space is something that contains names. You can create new
  -- name spaces and bring names from a name space into scope.
  module NameSpaces where

    -- To access definitions from a module in a different file, you have to
    -- 'import' this module. Only top-level modules (which have their own
    -- files) can be imported.

    -- If the imported module is not parameterised a name space with the same
    -- name as the module is created.
    import examples.syntax.ModuleA

    -- We can now refer to things from ModuleA using the created name
    -- space.  Note that no unqualified names were brought into scope
    -- (except, perhaps, the name of the name space). [To bring
    -- unqualified names into scope we have to use the 'open'
    -- declaration.]
    FunnyNat = examples.syntax.ModuleA.Nat

    -- If the name of an imported module clashes with a local module we might
    -- have to rename the module we are importing
    import examples.syntax.ModuleA as A
    import examples.syntax.ModuleA as A' using (Nat)

    Nat1 = A.Nat
    Nat2 = A'.Nat

    {- You can't project from a parameterised module. It has to be
       instantiated first. The only thing that happens when importing
       is that the module name 'examples.syntax.ModuleB' is brought
       into scope (and the type checker goes away and type checks this
       module).
    -}
    import examples.syntax.ModuleB

    -- To instantiate ModuleB we need something to instantiate it with.
    postulate X	   : Set
	      (==) : X -> X -> Prop
	      refl : (x : X) -> x == x

    -- To instantiate a module you create a new module and define it as the
    -- instantiation in question.
    module B = examples.syntax.ModuleB X (==) refl

    -- Now the module B contains all the names from ModuleB.
    XList = B.List
    And	  = B./\    -- qualified operators are not infix symbols

    dummyX = B.SubModule.dummy	-- submodules of ModuleB are also in scope

    -- This of course works for non-parameterised modules as well.
    module B' = B

    -- And you can create parameterised modules this way.
    module BX ((==) : X -> X -> Prop)(refl : (x : X) -> x == x) = B X (==) refl

    -- To bring names from a module into scope you use an open declaration.
    open examples.syntax.ModuleA

    two : FunnyNat
    two = eval (plus (suc zero) (suc zero))

    {- In all three declarations (import, module instantiation and open) you
       can give modifiers that affect the names which are imported. There are
       three modifiers:

	using (x1;..;xn)		only import x1,..,xn
	hiding (x1;..;xn)		import everything but x1,..,xn
	renaming (x1 to y1;..;xn to yn)	import x1,..,xn but call them y1,..,yn

      Restrictions:
	- a modifier can appear only once
	- 'using' and 'hiding' cannot appear together
	- imported names must be distinct (e.g. you cannot rename to a name
	  that is already being imported).
    -}

    -- B1 only contains True and False
    module B1 = B using (True; False)

    -- B2 contains True, False and And where And = B./\
    module B2 = B using (True; False) renaming (/\ to And)

    -- B3 contains everything from B except reflEqList and eqList, plus ===
    -- where (===) = B.eqList.
    module B3 = B hiding (reflEqList) renaming (eqList to ===)

    -- When referring to sub modules you have to be explicitly about it being
    -- a module
    module B4 = B renaming (module SubModule to Sub)

    dummy : X
    dummy = B4.Sub.dummy

  -- There are two kinds of meta variables; question marks and underscores.
  -- Question marks are used for interaction and underscores for implicit
  -- arguments.
  module MetaVariables where

    postulate X : Set
	      x : X

    -- There are two ways of writing a question mark: ? and {! ... !}
    -- The type checker will not complain about unsolved question marks (unless
    -- you claim you are done).
    incomplete : {A:Set} -> A -> A
    incomplete x = ?

    incomplete' : {A:Set} -> A -> A
    incomplete' x = {! you can put anything in here,
		       even {! nested holes !}
		    !}

    -- Underscores should always be solvable locally. Internally underscores
    -- are inserted for implicit arguments, but there are cases where you would
    -- like to write them explicitly. For instance, if you want to give one but
    -- not all implicit arguments to a function explicitly.
    underscore : ({A,B,C:Set} -> (A -> A) -> B -> C) -> X
    underscore f = f {_} {X} {_} (\y -> y) x

    -- Note that '_' is not an identifier character. The current use of
    -- underscore is not the real reason for this. The idea is rather that
    -- underscore will be used for subscripts.
    id : (A : Set) -> A -> A
    id A x = x

    x' = id_x -- this means id _ x

  -- The parser supports four types of literals. The syntax is the same as in
  -- Haskell (since that meant I could steal the lexer for them from ghc).
  module Literals where

    -- We haven't decided how to handle built-in types.
    postulate Integer : Set
	      Char    : Set
	      String  : Set
	      Float   : Set

    fortyTwo : Integer
    fortyTwo = 42

    helloWorld : String
    helloWorld = "Hello World!"

    escape : Char
    escape = '\ESC'

    pi : Float
    pi = 3.141592

  -- There are few things that the parser doesn't implement.

    {- Fancy case. I haven't been able to come up with a nice syntax for the
       fancy case statement.  The difficulty is that we should make it clear
       what arguments to the elimination rule will appear as patterns (the
       targets). Suggestions are welcome.

       Also I'm not sure that we want the fancy case. It would be better to
       have a good way of doing actual pattern matching on inductive families.
    -}

    {- Relative imports. You might want to be able to say

	import .ModuleA

       to import the module 'current.directory.ModuleA'. Easy to implement but
       I'm not sure it's that painful to write the complete name (not a problem
       in Haskell for instance). Drawbacks: it looks kind of funny and it adds
       an extra bit of syntax to remember.
    -}

