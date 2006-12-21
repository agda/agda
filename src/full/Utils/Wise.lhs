> {-# OPTIONS -fglasgow-exts -fallow-undecidable-instances -cpp #-}

Posted by Conor McBride on libraries@haskell.org Oct 23 2006.
(http://www.haskell.org/pipermail/libraries/2006-October/005950.html)

> module Utils.Wise where

Perhaps it's quite foolish, but here's an exercise in modifying one's
manners. I would not presume to use the title of this module as an
adjective, but I rather like it as a /suffix/.

> import Control.Applicative
> import Data.Traversable
> import Data.Monoid

Firstly, we shall need a useful little type class to capture the pattern
of using a special isomorph of a type to indicate not merely its raw data,
but also its relevant structure.

> class Unpack p u | p -> u where
>   unpack :: p -> u
>   (~~) :: (u -> p) -> p -> u
>   (~~) _ = unpack

The idea is that the packed type |p| is a special-purpose relabelling
of some duller unpacked type |u|. We thus expect |p| to determine |u|,
but a given |u| may have many such |p|'s, eg |Sum Int| and |Product
Int|, from |Data.Monoid|, wrapping Int to indicate an intended
|Monoid| structure.

Let's have an example:

> newtype Id x = Id {getId :: x}

> instance Unpack (Id x) x where
>   unpack (Id x) = x

The |(~~)| method is provided as a uniform way to make an explicit
inverse for the constructor. We can replace |getId| by |(Id ~~)|, and
we never have to remember its name again, or even waste namespace on
it in the first place. It's sometimes ambiguous and often unreadable
to use unpack directly, when a specific instance is intended.

Here, the structure I want to make explicit via |Id| is the notion of
pure computation, normally left implicit. But pure computation iss as
good a notion of computation as any other and quite often better.

> instance Functor Id where
>   fmap f (Id x) = Id (f x)

> instance Applicative Id where
>   pure = Id
>   Id f <*> Id s = Id (f s)

We use |Id| to get ordinary |fmap| from the more general |traverse|,
explaining the manner of the traversal.

> myFMap :: Traversable c => (s -> t) -> c s -> c t
> myFMap f cs = Id ~~ traverse (Id . f) cs

Recall that |Applicative (Const m)| if |Monoid m|. Let us have

> instance Unpack (Const m x) m where
>   unpack (Const c) = c

> myCrush :: (Traversable c, Monoid m) => (s -> m) -> c s -> m
> myCrush m cs = Const ~~ traverse (Const . m) cs

Spotting the pattern? One more.

> instance Unpack (Endo x) (x -> x) where
>   unpack (Endo f) = f

> myFold :: Traversable c => (s -> t -> t) -> c s -> t -> t
> myFold f cs = Endo ~~ myCrush (Endo . f) cs

What are we doing here? We're specifying the manner in which we use a
structure-exploiting operator. We transform a function in a particular
way by wrapping the range of that function in the type which indicates
the structure to be exploited by the operator. We can capture this
pattern by writing a transformer-transformer, composing the original
function with a given packer, then composing the transformed function
with the determined unpacker.

> wise :: Unpack dp du =>
>   (bu -> bp) -> ((a -> bp) -> c -> dp) -> (a -> bu) -> c -> du
> wise way changes how = unpack . changes (way . how)

Third-order programming: it's a whole other order.

So, now we have hints to the appropriate structure as parenthetical
remarks:

> travMap :: Traversable f => (s -> t) -> f s -> f t
> travMap = (Id `wise`) traverse

> crush :: (Monoid m, Traversable f) => (s -> m) -> f s -> m
> crush = (Const `wise`) traverse

> travFold :: (Traversable f) => (a -> b -> b) -> f a -> b -> b
> travFold = (Endo `wise`) crush

And, to boot,

> instance Unpack Any Bool where
>   unpack (Any b) = b

> travExists :: (Traversable f) => (a -> Bool) -> f a -> Bool
> travExists = (Any `wise`) crush

> instance Unpack All Bool where
>   unpack (All b) = b

> travAll :: (Traversable f) => (a -> Bool) -> f a -> Bool
> travAll = (All `wise`) crush

> instance Unpack (Sum x) x where
>   unpack (Sum x) = x

> travSum :: (Num a, Traversable f) => f a -> a
> travSum = (Sum `wise`) crush id

I'm in the mood for some pointwise lifting (in pointfree style).

> instance Unpack tp tu => Unpack (s -> tp) (s -> tu) where
>   unpack = (unpack .)

Now we can exploit the pointwise lifting of |Unpack| together with the
pointwise lifting of |Monoid|, yielding |travExists2|, a function which
checks out whether any pair of elements drawn respectively from two
traversable structures satisfies a relation. For example,
|travExists2 (==)| will check if the two structures have an element in
common.

> travExists2 :: (Traversable f, Traversable g) =>
>   (a -> b -> Bool) -> f a -> g b -> Bool
> travExists2 = ((crush . (Any .)) `wise`) crush

How does it work? Well, we lift |r :: a -> b -> Bool| to
|(Any .) . r :: a -> b -> Any| to |crush . (Any .) . r :: a -> g b -> Any|.
Now, |g b -> Any| is a |Monoid| because Any is, so the outer crush lifts
us to an |f a -> g b -> Any|. Then the unpacker for |g b -> Any| takes the
returned function back to a |g b -> Bool|.

All of this goes to show that Haskell has taken us far beyond the
standard, unimaginative view of types that you see all over the
place. I mean the view 'We already know what the programs are and how
to run them; types just discriminate between good programs and bad
programs.' That's an appropriate view for a typed /core/ language, but
it misses so many great opportunities for a typed /programming/ language.
We program by exposing structure.

More to the point, locally, if we accept that some notion of type-level
function is here to stay, is it worth adopting Unpack as a uniform way
to work with those newtypes whose purpose is to indicate structure (as
opposed to those which are intended to encapsulate invariants)? I
don't know how wise 'wise' is, but I had fun playing with it. Unpack,
though, is something I makes heavy use of.

Thought I'd punt it out there...

