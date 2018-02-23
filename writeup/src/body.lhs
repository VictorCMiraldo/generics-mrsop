\section{Background}
\label{sec:genericprog}

  Before diving head first into our generic programming framework,
lets take a tour on the existing generic programming libraries. We
will be defining a generic |size| function in a couple different variants,
illustrating how different techniques relate and the nuances between them.
This will let us gradually build up to our framework, that borrows the good
ideas from the different approaches and combines them without losing anything.


\victor{I feel that we should mention \texttt{scrap your boilerplate} somehow,
we are almost talking about all of them, right? Regardless, we have a good
argument against them: they require 'Data' and 'Typeable', hence restrict
which external datatypes one can use}

\subsection{Pattern functors}
\label{sec:patternfunctors}

  Since version $7.2$, GHC supports some basic, off the shelf, generic
programming using \texttt{GHC.Generics}~\cite{Magalhaes2010}, 
which exposes the \emph{pattern functor} of a datatype. This
allows one to define a function for \emph{any} datatype by induction
on the structure of its representation using \emph{pattern functors}.

  These \emph{pattern functors} are parametrized versions of tuples,
sum types (|Either| in Haskell lingo), and unit, empty and constant functors. These provide
a unified view over data: the generic \emph{representation} of values.
The values of a suitable type |a| are translated to this representation
by the means of the |from :: a -> RepGen a| function.

Defining a generic |size| function that provides a measure for any 
value of a supported datatype, for instance, is done in two
steps. First, we define a class that exposes a |size| function
for values. Since we use a mix of classes for both ground types (of kind |*|)
and type constructors (of kind |* -> *|), we shall be explicit about
them in our class definitions.

\begin{myhs}
\begin{code}
class Size (a :: *) where
  size :: a -> Int
  default size  :: (Generic a , GSize (RepGen a))
                => a -> Int
  size = gsize . fromGen
\end{code}
\end{myhs}

  The |default| keyword instructs Haskell to use the provided
implementation whenever the constraint |(GenericGen a , GSize (RepGen a))| 
can be satisfied when declaring an instance for |Size a|.
In a nutshell, we are saying that if Haskell
is aware of a generic representation for values of type |a|,
it can use the generic size function instead of requiring the user
to write her own function. The |gsize| function, on the
other hand, operates on the representation of a datatype
That is our second piece we need to define. We will
do so by another class and will use the instance mechanism to encode
a definition by induction on the structure of the language of representations.
Here, they are \emph{pattern functors}.

\begin{myhs}
\begin{code}
class GSize (rep :: * -> *) where
  gsize :: rep x -> Int
instance GSize V1 where gsize _ = 0
instance GSize U1 where gsize _ = 1
instance (GSize f , GSize g) => GSize (f :*: g) where
  gsize (f :*: g) = gsize f + gsize g
instance (GSize f , GSize g) => GSize (f :+: g) where
  gsize (L1 f) = gsize f
  gsize (R1 g) = gsize g
\end{code}
\end{myhs}

  We still have to handle the cases were 
we might have an arbitrary type in a position, modelled by the
constant functor. We must require an instance of |Size|
so we can sucessfully tie the recursive knot.

\begin{myhs}
\begin{code}
instance (Size a) => GSize (K1 R a) where
  gsize (K1 a) = size a
\end{code}
\end{myhs}

  This technique of \emph{mutually recursive classes} is quite 
specific to \texttt{GHC.Generics} flavor of generic programming.
It is worthwhile to illustrate how the compiler would go about choosing
instances for computing |size (Bin (Leaf 1) (Leaf 2))|:

\begin{align*}
  |size (Bin (Leaf 1) (Leaf 2))| 
    &= |gsize (from (Bin (Leaf 1) (Leaf 2)))| \\
    &= |gsize (R1 (K1 (Leaf 1) :*: K1 (Leaf 2)))| \\
    &= |gsize (K1 (Leaf 1)) + gsize (K1 (Leaf 2))| \\
    &= |size (Leaf 1) + size (Leaf 2)| \tag{$\dagger$}\\
    &= |gsize (from (Leaf 1)) + gsize (from (Leaf 2))|\\
    &= |gsize (L1 (K1 1)) + gsize (L1 (K1 2))|\\
    &= |size (1 :: Int) + size (2 :: Int)|   
\end{align*}

  Were we a compiler, we would hapilly issue a \texttt{"No instance
for (Size Int)"} error message at this point. Nevertheless, the
literals of type |Int| illustrate what we call \emph{opaque types}:
those types that constitute the base of the universe and are
\emph{opaque} to the representation language.

  One interesting aspect we should note here is the clearly
\emph{shallow} encoding that |from| provides. That is, we only
represent \emph{one layer} of recursion at a time. For example, in
$(\dagger)$, after unwrapping the calculation of the first
\emph{layer}, we are back to having to calculate |size| for |Bin Int|,
not their representation.

\victor[victor:codes]{In \texttt{GHC.Generics}, the representation has NO CODE;
in fact, that's why we need instance search to perform induction on it.}

  Upon reflecting on the generic |size| function we shown, one can see
a number of issues. Most notably is the amount of boilerplate to
achieve a conceptually simple task: sum up all the sizes of the fields
of whichever constructors make up the value. This is a direct
consequence of not having access to the \emph{sum-of-products}
structure that Haskell's |data| declarations follow. We will see a
different approach, tackling that issue, in
\Cref{sec:explicitsop}.  A second issue is the fact that the
generic representation does not carry any information about the
recursive structure of the type.  Instead, we are relying on the
instance search mechanism to figure out that the recursive arguments
can be consumed with the |default size| function. The
\texttt{regular}~\cite{Noort2008} addresses this issue by having a
specific \emph{pattern functor} for recursive positions.


\victor{Should we show how this is 'unsafe' by not having codes.
|Maybe :*: K1 R Int| is a pattern functor; instance search will blow up though;
or just mentioning is enough?}
  Perhaps even more subtle, but also more worrying, is that we have no
guarantees that the |RepGen a| of a type |a| will be defined using
only the supported \emph{pattern functors}. Fixing this would require
one to pin down the language that the representations follow, that is,
the \emph{code} of the datatype, whose semantics give rise to the
\emph{representation} of values. Besides correctnes issues, the
absence \emph{codes} greatly limits the number of generic combinators
one can define. Every generic function has to follow the
\emph{mutually recursive classes} technique we shown.

\subsection{Explicit Sums of Products}
\label{sec:explicitsop}

  Had we had access to a representation of the \emph{sum-of-products}
structure of |Bin|, we could have defined our |gsize| function as we
described it before: sum up the sizes of the fields inside a value,
ignoring the constructor. In fact, the
\texttt{generics-sop}~\cite{deVries2014} library allows one to do so.
Unlike \texttt{GHC.Generics}, the representation of values is
defined by induction on the \emph{code} of a datatype, this \emph{code}
is a type-level list of lists of |*|, whose semantics is
consonant to a formula in disjunctive normal form.  The outer list is
interpreted as a sum and the each of the inner lists as products.
This section provides an overview of \texttt{generic-sop} as required
to understand our techniques, we refer the reader to the original
paper~\cite{deVries2014} for a more comprehensive explanation.

This additional portion of information allows for a plethora of combinators
to be written. It ultimately allows one to write, with a pinch of
sugar, the |gsize| function as:

\begin{myhs}
\begin{code}
gsize :: (GenericSOP a) => a -> Int
gsize  = sum . elim (map size) . fromSOP
\end{code}
\end{myhs}

  Ignoring the details of the improved |gsize| for a moment, let us focus
on the high level structure. Remembering that |from| now
returns a \emph{sum-of-products} view over the data,
we are using an eliminator, |elim|, do apply a function to the fields
of whatever constructor makes up the value. This eliminator then applies
|map size| to the fields of the constructor, returning something akin
to a |[Int]|. We just need to |sum| them up to obtain the final
size.

  As we hinted earlier, the generic codes consists in 
a type-level list of lists. The outer list represents the 
constructors of a type, and will be interpreted as a $n$-ary sum, whereas
the inner lists are interepreted as the fields of the respective constructors,
interpreted as $n$-ary products.

\begin{myhs}
\begin{code}
type family    CodeSOP (a :: *) :: P ([ (P [*]) ])

type instance  CodeSOP (Bin a) = P ([ P [a] , P ([Bin a , Bin a]) ])
\end{code}
\end{myhs}

  Back when we were using \emph{pattern functors}, these could be
assembled in any order, we did not even have guarantee that the
arguments to \emph{pattern functors} were themselves \emph{pattern
functors} again! And this is what made the handling of the generic
representations tedious. Now, each datatype has a \emph{code},
|CodeSOP|, which is then interpreted giving rise to the
\emph{representation} of the values fo the datatype in question. T he
key insight here is that we can write combinators that work for
\emph{any} \emph{representation} by induction on the |CodeSOP|, and
this does not require instance search, that is, the definition
of a |GSize| instance for each \emph{pattern functor}.

  Expectedly, the very \emph{representation}, defined by induction on
|CodeSOP| by the means of $n$-ary sums, |NS|, and $n$-ary products,
|NP|.  These are parametrized by a functor to allow us to use them as
building blocks. 
  Overlooking a slight abuse of notation, one can look at |NS| and |NP|
through the lens of the following isomorphisms:

\begin{align*}
  | NS f [k_1 , k_2 , dots]| &\equiv |f k_1 :+: (f k_2 :+: dots)| \\
  | NP f [k_1 , k_2 , dots]| &\equiv |f k_1 :*: (f k_2 :*: dots)| 
\end{align*}

  We could then define the representation |RepSOP| to be
|NS (NP (K1 R))|, echoing the isomoprihms above, where |data K1 R a = K1 a| 
is being borrowed from \texttt{GHC.Generics}. 
This would then be exactly the representation we get
from \texttt{GHC.Generics}.

\begin{align*}
  |RepSOP (Bin a)|
  &\equiv | NS (NP (K1 R)) (CodeSOP (Bin a))| \\
  &\equiv |K1 R a :+: (K1 R (Bin a) :*: K1 R (Bin a))| \\
  &\equiv |RepGen (Bin a)|
\end{align*}

  It makes no sense to go through all the trouble of adding the
explicit \emph{sums-of-products} structure to simply forget this
information in the representation, however. Indeed, instead of
piggybacking on \emph{pattern functors}, we define |NS| and |NP| from
scratch using \emph{GADTs}~\cite{Xi2003}, whom play a central role
here.  By pattern matching on the values of |NS| and |NP| we are
informing the typechecker of the structure of the |CodeSOP|.

  An $n$-ary sum |NS f [k_1 , k_2 , dots]|, isomorphic to |Either (f
k_1) (Either (f k_2) dots)|, and an $n$-ary product |NP f [k_1 , k_2 ,
dots]|, isomorphic to |(f k_1 , f k_2 , dots)|, are defined as
follows:

\begin{minipage}[t]{.45\textwidth}
\begin{myhs}
\begin{code}
data NS :: (k -> *) -> [k] -> * where
  Here   :: f k      -> NS f (k (P (:)) ks)
  There  :: NS f ks  -> NS f (k (P (:)) ks)
\end{code}
\end{myhs}
\end{minipage}\begin{minipage}[t]{.45\textwidth}
\begin{myhs}
\begin{code}
data NP :: (k -> *) -> [k] -> * where
  NP0  ::                    NP f (P [])
  :*   :: f x -> NP f xs ->  NP f (x (P (:)) xs)
\end{code}
\end{myhs}
\end{minipage}

  Finally, since our atoms are of kind |*|, we can use the identity
functor, |I|, to interpret those and can finally define the representation
of values of a type |a| under the \emph{SOP} view:

\begin{myhs}
\begin{code}
type RepSOP a = NS (NP I) (CodeSOP a)

newtype I (a :: *) = I { unI :: a }
\end{code}
\end{myhs}

  Evidentiating the claim that one can define general combinators for
working with these representations, let us look at a couple of those
combinators. In particular, lets wrte the |elim| and |map| that were
used for the |gsize| function in the beginning of the section.

\begin{minipage}[t]{.45\textwidth}
\begin{myhs}
\begin{code}
elim :: (forall k dot f k -> a) -> NS f ks -> a
elim f (Here   x)  = f x
elim f (There  x)  = elim f x
\end{code}
\end{myhs}
\end{minipage}\begin{minipage}[t]{.45\textwidth}
\begin{myhs}
\begin{code}
map :: (forall k dot f k -> a) -> NP f ks -> [a]
map f  NP0        = []
map f  (x :* xs)  = f x : map f xs
\end{code}
\end{myhs}
\end{minipage}

  Comparing to the \texttt{GHC.Generics} implementation of |size|, we
see two improvements: (A) we need one less typeclass, namelly |GSize|,
and, (B) the definition is combinator-based. Considering that the
generated \emph{pattern functor} representation of a Haskell datatype
will already be in a \emph{sums-of-products}, we do not lose anything
by enforcing this structure.

  There are still downsides to this approach. A notable one being the need
to carry constraints arround. The actual |gsize| one would
write with \texttt{generics-sop} library, adding no sugar, looks like:

\begin{myhs}
\begin{code}
gsize :: (Generic a , All2 Size (CodeSOP a)) => a -> Int
gsize = sum . hcollapse . hcmap (Proxy :: Proxy Size) (mapIK size) . fromSOP
\end{code}
\end{myhs}

  The |All2 Size (CodeSOP a)| constraint tells the compiler that
all of the types serving as atoms for |CodeSOP a| are an instance of |Size|.
In our case, |All2 Size (CodeSOP (Bin a))| expands to |(Size a , Size (Bin a))|.
The |Size| constraint also has to be passed around with a |Proxy| for the
eliminator of the $n$-ary sum. This is a direct consequence of a \emph{shallow}
encoding: since we only unfold one layer of recursion at a time, we have to 
carry proofs that the recursive arguments can also be translated to
a generic representation. We can relief this burden by recording,
explicitely, which fields of a constructor are recursive or not.

\section{Explicit Fix: Deep and Shallow for free}
\label{sec:explicitfix}

  Introducing information about the recursive positions in a type is
done by changing the type of atoms in the universe. In
\Cref{sec:explicitsop} we had |CodeFix :: * -> (P [ (P [*])])|,
that is, the atoms of the universe were Haskell types. If instead we
create a new kind |Atom|, we can record wether or not a constructor
field is a recursive position or an opaque type.

\begin{myhs}
\begin{code}
data Atom = I | KInt | dots

type family    CodeFix (a :: *)   ::  P [ P [Atom] ]

type instance  CodeFix (Bin Int)  =   P [ P [KInt] , P [I , I] ]
\end{code}
\end{myhs}

  Where |I| is used to mark the recursive positions and |KInt, dots|
are codes for a pretermined selection of primitive types, which we
refer to as \emph{opaque types}.
Favoring the simplicity of the presentation, we will stick with only
hardcoded |Int| as the only opaque type in the universe. Later on,
in \Cref{sec:konparameter}, we parametrize the whole development to whatever
the user requires.

  The most notable difference is that our code now is not polymorphic.
Back in \Cref{sec:explicitsop} we have defined |CodeSOP (Bin
a)|, and this would work for any |a|. This might seen like a
disadvantage, but it is in fact quite the opposite. This allows us to
provide a deep conversion for free, given a shallow conversion. Beyond
doubt one needs to have access to the |CodeSOP a| when converting a
|Bin a| to its (deep) representation. By specifying the types involved
beforehand, we are able to get by without having to carry all of the
constraints we needed in \Cref{sec:explicitsop}. We can benefit
the most from this in the simplicity of combinators we are able to write.

  The representation of our codes now requires a functor that map |Atom|s into
Haskell values, that is, |Atom -> *|. The representation |RepFix| is remarkably 
similar to |RepSOP|, but since we now know the recursive positions, we are
able to lift the representation to a functor. In fact, it is a nice exercise to
write the |Functor (RepFix a)| instance. We are using a |newtype| here so
we can partially apply |RepFix|.

\begin{myhs}
\begin{code}
data NA :: * -> Atom -> * where
  NA_I :: x    -> NA x I
  NA_K :: Int  -> NA x KInt

newtype RepFix a x = Rep { unRep :: NS (NP (NA x)) (Code a) }
\end{code}
\end{myhs}

  Wrapping our |to| and |from| isomorphism into a typeclass and writing the
instance that witnesses that |Bin Int| has a |CodeFix| and is isomorphic
to its representation is quite straight worward.

\begin{myhs}
\begin{code}
class GenericFix a where
  from  :: a -> RepFix a a
  to    :: RepFix a a -> a
\end{code}
\end{myhs}

\begin{myhs}
\begin{code}
type instance CodeFix (Bin Int) = P [ P [KInt] , P [I , I] ]
instance Generic (Bin Int) where
  from (Leaf x)   = Rep (        Here  (NA_K x  :* NP0))
  from (Bin l r)  = Rep (There ( Here  (NA_I l  :* NA_I r :* NP0)))
\end{code}
\end{myhs}

  Note how |RepFix| still is a shallow representation. But by
constructing the least fixpoint of |RepFix a| we can obtain the deep
encoding for free, by simply recursively translating each
layer of the shallow encoding.

\begin{myhs}
\begin{code}
newtype Fix f = Fix { unFix :: f (Fix f) }

deepFrom :: (Generic a) -> a -> Fix (RepFix a)
deepFrom = Fix . fmap deepFrom . from
\end{code}
\end{myhs}

  So far, we are handling the same class of types
as \texttt{regular}~\cite{Noort2008}, but we are imposing 
the representation to follow a \emph{sum-of-products} structure
by the means of |CodeFix|. Those types are guaranteed to have
initial algebra, and indeed, the generic fold is defined
as expected: 

\begin{myhs}
\begin{code}
fold :: (RepFix a b -> b) -> Fix (RepFix a) -> b
fold f = f . fmap (fold f) . unFix
\end{code}
\end{myhs}

  With a solid representation that not only is guaranteed to follow a 
\emph{sum-of-products} structure but also has specific information about
the recursive positions of a type, it is trivial to define even the most
expressive combinators. One such example is the |compos| function, which 
applies a function |f| everywhere on the recursive structure.

\begin{myhs}
\begin{code}
compos :: (Generic a) => (a -> a) -> a -> a
compos f = to . fmap f . from
\end{code}
\end{myhs}

  Although more interesting in the mutually recursive setting,
\Cref{sec:family}, we can illustrate its use for traversing a
tree and adding one to its leaves. In fact, a very convoluted way of
writing |fmap (+1) :: Bin Int -> Bin Int| could be:

\begin{myhs}
\begin{code}
example :: Bin Int -> Bin Int
example (Leaf n)  = Leaf (n + 1)
example x         = compos example x
\end{code}
\end{myhs}

  It is worth nothing the \emph{catch-all} case, allowing one to
focus only on the interesting patterns and getting the traversal
of the rest of the datatype for free.
  
  Sometimes we actually want to consume a |Bin Tree| and produce
a single value, but does not need the full expressivity of |fold|. 
Instead, if we know how to consume the opaque types and combine
those results, we can consume any |GenericFix| type.

\begin{myhs}
\begin{code}
crush :: (Generic a) => (forall x dot Atom KInt x -> b) -> ([b] -> b) -> a -> b
crush k cat = crushFix . deepFrom
  where
    crushFix :: Fix (RepFix a) -> b
    crushFix = cat . elimNS (elimNP go) . unFix

    go (NA_I x) = crushFix x
    go (NA_K i) = k i
\end{code}
\end{myhs}

  Finally, we can revisit our running |gsize| example. With the current setting
one can write the simplest generic size function so far:

\begin{myhs}
\begin{code}
gsize :: (Generic a) => a -> Int
gsize = crush (const 1) sum
\end{code}
\end{myhs}

  The deep encoding of |a| allows us to drop the complicated constraints needed
for handling the types of the fields of the constructors of |a|. The information
about the recursive position allows us to write neat combinators like |crush|.
The only thing keeping us from handling real life applications is the limited
form of recursion. When a user requires a generic programming
library, chances are they need to traverse and consume mutually recursive
structures.

\victor{Should we introduce the |sop| function and |View| datatype?}

\section{Mutual Recursion}
\label{sec:family}

  Conceptually, going from regular types, \Cref{sec:explicitfix}, to
mutually recursive families is simple. We just need to be able to reference
not only one type variable, but one for each element in the family.
As a running example, we use the flattened |RoseTree| family described in the
introduction:
\begin{myhs}
\begin{code}
data RoseTree      a  =  a :>: RoseTreeList a
data RoseTreeList  a  =  NilRoseTree | RoseTree a ConsRoseTree RoseTreeList a
\end{code}
\end{myhs}

The previously introduced |CodeFix| does not provide enough combinators to
describe this datatype. In particular, when we try to write
|CodeFix (RoseTree Int)|, there is no immediately recursive appearance of
|RoseTree| itself, so we cannot use the atom |I| in that position.
|RoseTreeList a| is not an opaque type either, so we cannot
use any of the other combinators provided by |Atom|. Furthermore, we would
like to not forget about |RoseTree Int| referring to itself via another datatype
|RoseTreeList|.

Our solution is to move from codes of datatypes to \emph{codes for families of
datatypes}. We no longer talk about |CodeFix (RoseTree Int)| or
|CodeFix (RoseTreeList Int)| in isolation, but rather about
|CodeMRec (P [RoseTree Int, RoseTreeList Int])|. Then we extend the language
of |Atom|s by appending to |I| a natural number which specifies which is
the member of the family in which recursion happens:
\begin{myhs}
\begin{code}
data Atom = I Nat | KInt | dots

data Nat  = Z | S Nat
\end{code}
\end{myhs}
The code of this recursive family of datatypes can be finally described as:
\begin{myhs}
\begin{code}
CodeMRec (P [RoseTree Int, RoseTreeList Int]) = (P  [ (P [ (P [ KInt, I (S Z)])])          -- code for RoseTree Int
                                                    , (P [ (P []), P [ I Z, I (S Z)]])])   -- code for RoseTreeList Int
\end{code}
\end{myhs}
Let us have a closer look at the code for |RoseTree Int|, which appears in the
first place in the list. There is only one constructor which has an |Int| field,
represented by |KInt|, and another in which we recur to the second member of 
our family (since lists are 0-indexed, we represent this by |S Z|). Similarly,
the second constructor of |RoseTreeList Int| points back to both |RoseTree Int|
using |I Z| and to |RoseTreeList| itself via |I (S Z)|.

  Having settled on the definition of |Atom|, we now need to adapt |NA| to
the new |Atom|s. In order to interpret any |Atom| into |*|, we now need
a way to interpret the different recursive positions. This information is given
by an additional type parameter |phi| from natural numbers into types.
\begin{myhs}
\begin{code}
data NA :: (Nat -> *) -> Atom -> * where
  NA_I :: phi n  -> NA phi (I n)
  NA_K :: Int    -> NA phi KInt
\end{code}
\end{myhs}
The additional |phi| bubbles up to the representation of codes.
\begin{myhs}
\begin{code}
type RepMRec (phi :: Nat -> *) (c :: [[Atom]]) = NS (NP (NA phi)) c
\end{code}
\end{myhs}
The only missing piece is tying the recursive loop here. If we want our
representation to describe a family of datatypes, |phi| should be the functor
interpreting each of those types.

As an ancillary operation, we need a type-level lookup function for the family.
We can define this operation for any type-level list in Haskell by
means of a \emph{closed} |type family| which we call |Lkup|.
\begin{myhs}
\begin{code}
type family Lkup (ls :: [k]) (n :: Nat) :: k where
  Lkup (P [])    _          = TypeError "Index out of bounds"
  Lkup (x : xs)  (P Z)      = x
  Lkup (x : xs)  ((P S) n)  = Lkup xs n
\end{code}
\end{myhs}
In order to improve type error messages, we generate a |TypeError| whenever we
reach the given index |n| is out of bounds. Interestingly, our design
guarantees that this case is never reached, all lookups in a representation
of a code all well-typed.

In principle, this is enough to provide a ground representation for the family
of types. Let |fam| be the family of ground types, like
|(P [RoseTree Int, RoseTreeList Int])|, and |codes| the corresponding list
of codes. Then the representation of the type at index |ix| in the list |fam|
is given by:
\begin{myhs}
\begin{code}
RepMRec (Lkup fam) (Lkup codes ix)
\end{code}
\end{myhs}
This definition states that to obtain the representation of the type at index
|ix|, we first lookup its code. Then, in the recursive positions we interpret
each |I n| by looking up the type at that index in the original family. This
gives us a \emph{shallow} representation. As an example, here is the expansion
for index 0 of the rose tree family:
\begin{myhs}
\begin{code}
RepMRec (Lkup RoseTreeFamily) (Lkup RoseTreeCodes Z)
  =    NS (NP (NA (Lkup RoseTreeFamily))) (Lkup RoseTreeCodes Z)
  =    NS (NP (NA (Lkup RoseTreeFamily))) (P [ (P [ KInt, I (S Z)])])
  ==   K1 R Int :*: K1 R (Lkup RoseTreeFamily (S Z))
  =    K1 R Int :*: K1 R (RoseTreeList Int)
\end{code}
\end{myhs}

Unfortunately, Haskell only allows saturated, that is, fully-applied type
families. As a result, we need to introduce an intermediate datatype |El|,
\begin{myhs}
\begin{code}
data El :: [*] -> Nat -> * where
  El :: Lkup fam ix -> El fam ix
\end{code}
\end{myhs}
The representation of the family |fam| at index |ix| is thus given by
|RepMRec (El fam) (Lkup codes ix)|. We only need to use |El| in the first
argument, because that is the position in which we require partial application.
The second position features |Lkup| fully-applied, and can stay as is.

  Up to this point, we have talked about a type family and their codes as 
independent entities. As in the rest of generic programming approaches, we
want to make their relation explicit. The |Family| type class realizes this
relation, and introduces functions to perform the conversion between our
representation and the actual types:
\begin{myhs}
\begin{code}
class Family (fam :: [*]) (codes :: [[[Atom]]]) where
  
  fromMRec  :: SNat ix  -> El fam ix                         -> RepMRec (El fam) (Lkup codes ix)
  toMRec    :: SNat ix  -> RepMRec (El fam) (Lkup codes ix)  -> El fam ix
\end{code}
\end{myhs}
One of the differences between other approaches and ours is that we do not
use an associated type to define the |codes| for a mutually recursive family
|fam|. One of the reasons to choose this path is that it alleaviates the
nomenclature burden of writing the longer |CodeMRec fam| everytime we want to
refer to |codes|. Furthermore, there are types like lists which appear in
many different families, and in that case it makes more sense to speak about a
relation instead of a function. In any case, we can choose the other point of
the design space by moving |codes| into an associated type or introduce a
functional dependency |fam -> codes|.

Since now |fromMRec| and |toMRec| operate on families of datatypes, they have
to specify how to translate \emph{each} of the members of the family back and
forth the generic representation. This translation needs to know which is the
index of the datatype we are dealing with in each case, this is the reason
underneath the additional |SNat ix| parameter. For example, in the case of
or family of rose trees, |fromMRec| has the following shape:
\begin{myhs}
\begin{code}
fromMRec SZ       (El (x :>: children))  = Rep (          Here (NA_K x :* NA_I children :* NP0))
fromMRec (SS SZ)  (El [])                = Rep (          Here NP0 ))
fromMRec (SS SZ)  (El (x : xs))          = Rep ( There (  Here (NA_I x :* NA_I xs :* NP0)))
\end{code}
\end{myhs}
By pattern matching on the index, the compiler knows which is the family member
to expect as second argument. In dependently-typed languages such as Agda or
Idris, this index would be expressed as a normal |Nat| value,
\begin{myhs}
\begin{code}
fromMRec : (ix : Nat)  -> El fam ix -> RepMRec (El fam) (Lkup codes ix)
\end{code}
\end{myhs}
Alas, Haskell is not dependently-typed. The usual trick is to introduce a
\emph{singleton type} which reifies a type into its term-level representation.
In the case of |Nat|, this type is |SNat|,
\begin{myhs}
\begin{code}
data SNat (n :: Nat) where
  SZ ::          -> SNat (P Z)
  SS ::  SNat n  -> SNat ((P S) n)
\end{code}
\end{myhs}

  
\paragraph{Deep encoding.}
  The least fixpoint combinator also receives an extra parameter of kind |Nat -> *|:

\begin{myhs}
\begin{code}
newtype Fix (codes :: [[[Atom]]]) (ix :: Nat)
  = Fix { unFix :: RepMRec (Fix codes) (Lkup codes ix) }
\end{code}
\end{myhs}

\victor{Explain SNat}
\victor{Explain we could make another class that checks that
the list of codes is well formed w.r.p.t the family, retaining
all the static guarantees we love so much in Haskell}


Lifting the construction from \Cref{sec:explicitfix} starts by
redefining |Atom| to something like:

\begin{myhs}
\begin{code}
data Atom (n :: Nat) 
  = I (Fin n)
  | KInt
  | dots
\end{code}
\end{myhs}

  Where |Fin n| is a type isomorphic to a finite set with |n| elements. Unfortunately 
this approach has a major drawback in Haskell. The lack of dependent types would
require us to turn on the \texttt{-XTypeInType} extension, which although does not
break consistency, can cause the compiler to loop and is generaly seen as an extreme
resort. Instead, we choose to relax the definition of |Atom| to

\begin{myhs}
\begin{code}
data Atom  
  = I Nat 
  | KInt
  | dots
\end{code}
\end{myhs}
 
  One might naively think we are loosing type-safety by allowing codes
to reference an arbitrary number of recursive positions. What is
keeping the user from defining |CodeMRec (Rose Int) = (P [ (P [ KInt ,
I (S (S (S (S (S Z))))) ])])|?  Nothing! As a matter of fact that is a
perfectly valid code. Moreover, one can construct a family where this
code is not only valid, but also correct. As long as 
the interpretation of such code under the family |[Rose Int , [Rose
Int]]| is ill-typed, we are not compromising any safety and we remove
some boilerplate from the whole construction.


\subsection{Parametrized Opaque Types}
\label{sec:konparameter}

Talk about adding a kind |kon| and making everything
receive a |kon -> *| parameter, like in the actual implementation.

\subsection{Combinators}

  \victor{Assuming |RepMRec| now receives an interpretation of constants}
  \victor{glue this up; point is: |zip| |map| |elim| and |compos| are the base}


  For the sake of fostering intuition instead of worrying about
notational overhead, we shall write values of |RepMRec kappa phi c| just like
we would write normal Haskell values. They have the same \emph{sums-of-products} 
structure anyway. Whenever a function is defined
using the |^=| symbol, |C x_1 dots x_n| will stand for a value of the corresponding
|RepMRec phi c|, that is, |There (dots (Here (x_1 :* dots :* x_n :* NP0)))|. 
Since each of these |x_1 dots x_n| might be a recursive type or an opaque type,
whenever we have two functions |f_I| and |f_K| in scope, |fSq x_j| will
denote the application of the correct function for recursive positions, |f_I|,
or opaque types |f_K|.

  Through the rest of this section we wish to showcase a selection of particularly
powerful combinators that are remarkably simple to define by exploiting the
\emph{sums-of-products} structure. The first obvious such combinator is |map|.
Our |RepMRec kappa phi c| does not make a regular functor anymore, but a higher
bifunctor:

\begin{myhs}
\begin{code}
bimapRep  ::  (forall k   dot kappa1  k   -> kappa2  k) 
          ->  (forall ix  dot phi1    ix  -> phi2    ix) 
          ->  RepMRec kappa1 phi1 c -> RepMRec kappa2 phi2 c
bimapRep f_K f_I (C x_1 dots x_n) ^= C (fSq x_1) dots (fSq x_n)
\end{code}
\end{myhs}

  More interesting than a map perhaps is a general eliminator. In order to
destruct a |RepMRec kappa phi c| we need a way for eliminating every recursive position
or opaque type inside the representation and a way of combining these results. 

\begin{myhs}
\begin{code}
elimRep  ::  (forall k   dot kappa  k   -> a)
         ->  (forall ix  dot phi    ix  -> a)
         ->  ([a] -> b)
         ->  RepMRec kappa phi c -> b
elimRep f_K f_I cat (C x_1 dots x_n) ^= cat [ fSq x_1 , dots , fSq x_n ]
\end{code}
\end{myhs}

  Being able to eliminate a representation is useful, but it becomes even
more useful when we are able to combine the data in different values of
the same representation with a |zip| like combinator. Our |zipRep|
will attempt to put two values of a representation ``side-by-side'', as long
as they are constructed with the same injection into the $n$-ary sum, |NS|.

\begin{myhs}
\begin{code}
zipRep  :: Rep kappa1 phi1 c -> Rep kappa2 phi2 c -> Maybe (Rep (kappa1 :*: kappa2) (phi1 :*: phi2) c)
zipRep (C x_1 dots x_n) (D y_1 dots y_m)
  | C == D     ^= Just (C (x_1 :*: y_1) dots (x_n :*: y_n)) -- if C == D, then also n == m!
  | otherwise  ^= Nothing
\end{code}
\end{myhs}

  Note that it is trivial to write |zipRep| with an arbitrary
|(Alternative f)| constraint instead of |Maybe|. Another combinator
that receives a good boost in expressivity is the beloved |compos|,
introduced in \Cref{sec:explicitfix}. We are now able to change every
subtree of whatever type we choose inside an arbitrary value of the
mutually recursive family in question.

\begin{myhs}
\begin{code}
compos  :: (forall iy dot El fam iy -> El fam iy)
        -> El fam ix -> El fam ix
compos f = toMRec . mapRep f . fromMRec
\end{code}
\end{myhs}

  It is worth nothing that although we presented pure versions
of these combinators, \texttt{\nameofourlibrary} defines monadic
variants of these and suffixes them with a ``M'', following the
standard Haskell naming convention. We will need these monadic
combinators in \Cref{sec:alphaequivalence}.

\section{Examples}
\label{sec:mrecexamples}

\subsection{Equality}

  Following the unspoken law of generic programming papers,
one is obliged to define generic equality in one's generic programming
framework. Using \texttt{\nameofourlibrary} one can define a particularly
elegant version of generic equality:

\begin{myhs}
\begin{code}
geq ::  (Family kappa fam codes) 
    =>  (forall k dot kappa k -> kappa k -> Bool)
    ->  El fam ix -> El fam ix -> Bool
geq eq_K = go `on` deepFrom
  where
    go :: Fix codes ix -> Fix codes ix -> Bool
    go (Fix x) (Fix y)  = maybe False (elimRep (uncurry eq_K) (uncurry go) and) 
                        $ zipRep x y 
\end{code} %$
\end{myhs}

  Reading through the code we see that we convert both
arguments of |geq| to their deep representation, then compare their
top level constructor with |zipRep|, if their constructor agrees
we go through each of their fields calling either the equality on
opaque types |eq_K| or recursing.

\subsection{$\alpha$-Equivalence}
\label{sec:alphaequivalence}

  Syntatic equality is definitely a must, but it is a ``no sweat''
application of generic programming. A more involved exercise,
requiring some muscle, is the definition of
\emph{$\alpha$-equivalence} for a language. On this section we start
showing a straight forward version for the $\lambda$-calculus then go
on to a more elaborate language.

  Regardless of the language, determining whether two programs are
$\alpha$-equivalent requires one to focus on the the constructors that
introduce scoping, declare variables or reference variables. All the
other constructors of the language should be trivial a trivial
combination of recursive results. Let us warm up with the
$\lambda$-calculus:

\begin{myhs}
\begin{code}
data Term  =  Var  String
           |  Abs  String  Term
           |  App  Term    Term
\end{code}
\end{myhs}

  The process is conceptually simple. Firstly, for |t_1, t_2 :: Term|
to be $\alpha$-equivalent, they have to have the same structure, that
is, the same constructors. Otherwise, we can already say they are not
$\alpha$-equivalent.  We then traverse both terms at the same time and
everytime we go through a binder, in this case |Abs|, we register a
new \emph{rule} saying that the bound variable names are equivalent
for the terms under that scope. Whenever we find a reference to a
variable, |Var|, we check if the referenced variable is either exactly
the same or equivalent under the registered \emph{rules} so far.

  Let us abstract away this book-keeping functionality by the means of
a monad with a couple associated functions. The idea is that |m| will
keep track of a stack of scopes, each scope will be registering a list
of \emph{name-equivalences}. In fact, this is very close to how one
sould go about defining equality for \emph{nominal terms}~\cite{Calves2008}.

\begin{myhs}
\begin{code}
class Monad m => MonadAlphaEq m where
  scoped    :: m a -> m a
  addRule   :: String -> String -> m ()
  (=~=)     :: String -> String -> m Bool
\end{code}
\end{myhs}

  Running a |scoped f| computation will push a new scope for running |f|
and pop it after |f| is done. The |addRule v_1 v_2| function registers an equivalence
of |v_1| and |v_2| in the top of the scope stack. Finally, |v_1 =~= v_2| is define
by pattern matching on the scope stack. If the stack is empty, then |v_1 =~= v_2 = v_1 == v_2|.
Otherwise, let the stack be |s:ss|. We first traverse |s| gathering the rules
referencing either |v_1| or |v_2|. If there is none, we check if |v_1 =~= v_2| under |ss|.
If there are rules referencing either variable name in the topmost stack, we must
ensure there is only one such rule, and it states a name equivalence between |v_1| and |v_2|.
We will not show the implementation of these functions as these can be checked in 
the \texttt{Examples} directory of \texttt{\nameofourlibrary}. It is a good exercise
to implement the |MonadAlphaEq (State [[ (String , String) ]])| nevertheless. 

  Returning to the main focus of this illustration and leaving book-keeping functionality
aside, we define our alpha equivalence decider by encoding what to do
for |Var| and |Abs| constructors. The |App| can be eliminated generically.

%format TermP  = "\HT{Term\_}"
%format VarP   = "\HT{Var\_}"
%format AbsP   = "\HT{Abs\_}"
\begin{myhs}
\begin{code}
alphaEq :: Term -> Term -> Bool
alphaEq x y = runState (galphaEq (deepFrom x) (deepFrom y)) [[]]
  where
    galphaEq x y = maybe False (go TermP) (zipRep x y)

    step = elimRepM  (return . uncurry (==))  -- Opaque types have to be equal!
                     (uncurry galphaEq)       -- recursive step
                     (return . and)           -- combining results

    go TermP x = case sop x of
      VarP (v_1 :*: v_2)                -> v_1 =~= v_2
      AbsP (v_1 :*: v_2) (t_1 :*: t_2)  -> scoped (addRule v_1 v_2 >> galphaEq t_1 t_2)
      _                                 -> step x
\end{code}
\end{myhs}

  There is a number of things going on with this example. First,
note the application of |zipRep|. If two |Term|s are made with different
constructors, |galphaEq| will already return |False| because |zipRep| will fail.
When |zipRep| succeeds though, we get access to one constructor with
paired fields inside. Then the |go| function enters the stage, it 
is performing the necessary semantic actions for the |Var| and |Abs|
constructors and applying a general eliminator for anything else.
The names suffixed with an underscore are \emph{pattern synonyms} 
that make programming in this framework more convenient. These are
also automatically generated as we will see on \Cref{sec:templatehaskell}.

  One might be inclined to believe that the generic programming here
is more cumbersome than a straight forward pattern matching definition
over |Term|.  If we bring in a more intricate language to the
spotlight, however, manual pattern matching becomes almost untractable
very fast.  Take the a toy imperative language defined below.
Transporting |alphaEq| from the lambda calculus is fairly simple. For
one, |alhaEq|, |step| and |galphaEq| remain the same.  We just need to
adapt the |go| function:

%format StmtP    = "\HT{Stmt\_}"
%format SAssignP = "\HT{SAssign\_}"
%format DeclP    = "\HT{Decl\_}"
%format DVarP    = "\HT{DVar\_}"
%format DFunP    = "\HT{DFun\_}"
%format ExpP     = "\HT{Exp\_}"
%format EVarP    = "\HT{EVar\_}"
%format ECallP   = "\HT{ECall\_}"
\begin{minipage}[t]{.45\textwidth}
\begin{myhs}
\begin{code}
data Stmt 
  =  SAssign  String  Exp 
  |  SIf      Exp     Stmt Stmt
  |  SSeq     Stmt    Stmt
  |  SReturn  Exp
  |  SDecl    Decl
  |  SSkip

data Decl 
  =  DVar String
  |  DFun String String Stmt

data Exp 
  =  EVar   String
  |  ECall  String  Exp
  |  EAdd   Exp     Exp
  |  ESub   Exp     Exp
  |  ELit   Int
\end{code}
\end{myhs}
\end{minipage}%
\begin{minipage}[t]{.50\textwidth}
\begin{myhs}
\begin{code}
go StmtP x = case sop x of
      SAssignP (v_1 :*: v_2) (e_1 :*: e_2)  
        -> addRule v_1 v_2 >> galphaEq e_1 e_2
      _ -> step x
go DeclP x = case sop x of
      DVarP (v_1 :*: v_2) 
        -> addRule v_1 v_2 >> return True
      DFunP (f_1 :*: f_2) (x_1 :*: x_2) (s_1 :*: s_2)
        -> addRule f_1 f_2   
        >> scoped (addRule x_1 x_2 >> galphaEq s_1 s_2)
      _ -> step x
go ExpP x = case sop x of
      EVarP (v_1 :*: v_2)
        -> v_1 =~= v_2
      ECallP (f_1 :*: f_2) (e_1 :*: e_2)
        -> (&&) <$$> f_1 =~= f_2 <*> galphaEq e_1 e_2 
      _ -> step x 
go _ x = step x
\end{code}
\end{myhs}
\end{minipage}

  And for this small toy language, having to write $\alpha$-equivalence
by pattern matching might not be so straight forward anymore. Moreover,
if we decide to change the toy language and add more statements or more expressions,
the changes to the |go| function are minimal, if any. As long as we do not touch
the constructors that |go| patterns matches on, we can use the very same function.

\subsection{The Generic Zipper}

  \victor{does the generic zipper deserves its own section or do
we just want to mention it without going into detail??
I'd say we wait and see how much space we need to fill up}

\section{Template Haskell}
\label{sec:templatehaskell}

\victor{I'm assuming we have already introduced the 
usual RoseTree family: |data Rose a = Fork a [Rose a]|}

\victor{The glue text should mention how boring and mechanical it is to 
have to write the |Family| instance by hand}

  Having a convenient and robust way to get the |Family| instance
for a certain selection of datatypes is paramount for the usability
of the library. The goal is to take mechanical work away from the
programmer, and not introduce more, after all. In a real scenario,
the typical mutually recursive family will be constituted of dozens
of datatypes with tens of dozens of constructors. Sometimes these
datatypes are written with parameters, or come from external libraries.
There are many difficulties to a fully automatic interface to deriving |Family|
instances.

\subsection{The Final User Interface}
\label{sec:thapi}

  All that the programmer have to do to derive their |Family|
instance is call the \emph{Template Haskell}~\cite{Sheard2002} 
function |deriveFamily| and pass the (fully saturated) type that
is the topmost type in the family:

\newcommand{\shspc}{\hspace{-0.05em}}
%format (tht (a)) = "\HSSym{[\shspc t\shspc|}" a "\HSSym{|\shspc]}"
\begin{myhs}
\begin{code}
data Exp   var = dots
data Stmt  var = dots
data Decl  var = dots
data Prog  var = dots

deriveFamily (tht (Prog String))
\end{code}
\end{myhs}

  \victor{Explain the splicing idea; mention that |Prog String| will
be the |Lkup Z Fam| type}

\subsection{Under the Hood}
\label{sec:underthehood}

  The process of deriving a whole mutually recursive family from a single
member is mainly divided in two disjoint process. First we unfold all definitions
and follow all the recursive paths until we reach a fixpoint and, hence,
have discovered all types in the family. Second, we translate the definition
of the previously discovered types to the format our library expects.

  Let us illustrate this process in a bit more detail using the cannonical
mutually recursive family example and walking through what
happens inside \emph{Template Haskell}~\cite{Sheard2002} when it starts unfolding 
the |deriveFamily| clause.

\begin{myhs}
\begin{code}
data Rose a  = a :>: [Rose a]
data [a]     = nil | a : [a]

deriveFamily (tht (Rose Int))
\end{code}
\end{myhs}

  \victor{I'm using type-level naturals in the following}
  

  The first thing that happens is registering the type |Rose Int| as being 
indexed by |Z|. But we have not yet processed it. We need to reify
the definition of |Rose| and apply it to |Int| in order to get the 
the type of |:>:| that will belong in the family. In fact, after reifying |Rose Int|
and $\beta$-reducing it we get something like 
|(\ a -> a :>: [Rose a]) Int == Int :>: [Rose Int]|. We now have to
process the fields of |Int :>: [Rose Int]|, and once we are done, convert them
to |Atom|s. The first field will be an opaque type |KInt|, but the second
needs further processing, as it is the first time we encounter the type |[Rose Int]|.
Same story as before. Start by registering |[Rose Int]| to a fresh index, in this case |S Z|.
Reify the topmost application and $\beta$-reduce: |(\ a -> nil || a : [a]) (Rose Int) ==| 
|nil || (Rose Int) : [Rose Int]|. We now go over the fields of each constructor
and see what still needs processing. Turns out we are done since there is no
type we have not seen before as both |Rose Int| and |[Rose Int]| have been
registered with indexes |Z| and |S Z| respectively. We can then issue
the codes:


\begin{myhs}
\begin{code}
type CodeRoseInt      = (P [ (P [ KInt , I (S Z) ]) ])
type CodeListRoseInt  = (P [ (P [ ]) , (P [ I Z , I (S Z) ]) ])
\end{code}
\end{myhs}

  \victor{I'm not sure I should delve in more details about
the actual implementation. Does the description suffice?}

  \victor{Should we talk about the generation of pattern synonyms
to help with the manipulation of deeply embedded values?}

\subsection{Temp. Summary}

  \victor{Stress that we have achieved what we were looking for:
\begin{description}
  \item[Convenience:] The user jsut tells the top-most type
    of the family. Changes in the family don't require changes
    in the code (unless they are gigantic changes, obviously).
  \item[Robustness:] Having a type-level reduction mechanism
    allows us to let the user make use of types such as |Maybe|
    or |[ ]| and the mechanism will consider those as members of
    the family.
\end{description}}


  In order to derive a whole mutually recursive family from just one of
the members of the family requires some engineering. 

We have to be able to automatically handle all of these cases for
a satisfying \emph{template haskell} mechanism.

\victor{Driving in Auto from Gameplan}

\section{Conclusion}

the usual stuff...