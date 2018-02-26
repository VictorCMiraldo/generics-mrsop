\section{Background}
\label{sec:genericprog}

  Before diving head first into our generic programming framework,
lets take a tour on the existing generic programming libraries. For that,
will be looking at a generic |size| function from a few different angles,
illustrating how different techniques relate and the nuances between them.
This will let us gradually build up to our framework, that borrows the good
pieces of each of the different approaches and combines them without compromising.

\victor{I feel that we should mention \texttt{scrap your boilerplate} somehow,
we are almost talking about all of them, right? Regardless, we have a good
argument against them: they require 'Data' and 'Typeable', hence restrict
which external datatypes one can use}

\subsection{GHC Generics}
\label{sec:patternfunctors}

  Since version $7.2$, GHC supports some basic, off the shelf, generic
programming using \texttt{GHC.Generics}~\cite{Magalhaes2010}, 
which exposes the \emph{pattern functor} of a datatype. This
allows one to define a function for a datatype by induction
on the structure of its representation using \emph{pattern functors}.

  These \emph{pattern functors} are parametrized versions of tuples,
sum types (|Either| in Haskell lingo), and unit, empty and constant functors. These provide
a unified view over data: the generic \emph{representation} of values.
The values of a suitable type |a| are translated to this representation
by the means of the |from :: a -> RepGen a|.

Defining a generic function is done in two
steps. First, we define a class that exposes the function
for arbitrary types, in our case, |size|.

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
implementation whenever none is provided and the constraint |(GenericGen a , GSize (RepGen a))| 
can be satisfied when declaring an instance for |Size a|.

The |gsize| function, on the other hand, operates on the representation of datatypes
, being the second piece we need to define. We use
another class and the instance mechanism to encode
a definition by induction on representations.
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
represent \emph{one layer} at a time. For example, in
$(\dagger)$, after unwrapping the calculation of the first
\emph{layer}, we are back to having to calculate |size| for |Bin Int|,
not their generic representation.

\victor[victor:codes]{In \texttt{GHC.Generics}, the representation has NO CODE;
in fact, that's why we need instance search to perform induction on it.}

  Upon reflecting on the generic |size| function above, we see
a number of issues. Most notably is the amount of boilerplate to
achieve a conceptually simple task: sum up all the sizes of the fields
of whichever constructors make up the value. This is a direct
consequence of not having access to the \emph{sum-of-products}
structure that Haskell's |data| declarations follow. 
A second issue is the fact that the
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
structure of |Bin|, we could have defined our |gsize| function just like
its informal description: sum up the sizes of the fields inside a value,
ignoring the constructor.
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
just on its high level structure. Remembering that |from| now
returns a \emph{sum-of-products} view over the data,
we are using an eliminator, |elim|, to apply a function to the fields
of whatever constructor makes up the value. This eliminator then applies
|map size| to the fields of the constructor, returning something akin
to a |[Int]|. We then |sum| them up to obtain the final
size.

  As we hinted earlier, the generic codes consists in 
a type-level list of lists. The outer list represents the 
constructors of a type, and will be interpreted as a sum, whereas
the inner lists are interepreted as the fields of the respective constructors,
interpreted as products.

\begin{myhs}
\begin{code}
type family    CodeSOP (a :: *) :: P ([ (P [*]) ])

type instance  CodeSOP (Bin a) = P ([ P [a] , P ([Bin a , Bin a]) ])
\end{code}
\end{myhs}

  Back when we were using \emph{pattern functors}, these could be
assembled in any order, we did not even have guarantee that the
arguments to \emph{pattern functors} were themselves \emph{pattern
functors} again! This made the handling of the generic
representations cumbersome. Now, each datatype has a \emph{code},
|CodeSOP|, which is then interpreted giving rise to the
\emph{representation} of the values of the datatype. The
key insight here is that we can write combinators that work for
\emph{any} \emph{representation} by induction on the |CodeSOP|, 
without using instances to explore the structure of the representation. 

  Expectedly, the very \emph{representation}, defined by induction on
|CodeSOP| by the means of generalized $n$-ary sums, |NS|, and $n$-ary products,
|NP|.  
  Overlooking a slight abuse of notation, one can view at |NS| and |NP|
through the lens of the following isomorphisms:
\begin{align*}
  | NS f [k_1 , k_2 , dots]| &\equiv |f k_1 :+: (f k_2 :+: dots)| \\
  | NP f [k_1 , k_2 , dots]| &\equiv |f k_1 :*: (f k_2 :*: dots)| 
\end{align*}

  We could then define the representation |RepSOP| to be
|NS (NP (K1 R))|, echoing the isomoprihms above, where |data K1 R a = K1 a| 
is being borrowed from \texttt{GHC.Generics}. 
This is exactly the representation we get
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

\victor{could add a note here saying that this is 
one of the central tricks}

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
functor, |I|, to interpret those and define the final representation
of values of a type |a| under the \emph{SOP} view:

\begin{myhs}
\begin{code}
type RepSOP a = NS (NP I) (CodeSOP a)

newtype I (a :: *) = I { unI :: a }
\end{code}
\end{myhs}

  Evidentiating the claim that one can define general combinators for
working with these representations, let us look at |elim| and |map|,
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

\victor{We need some glue here}
  Comparing to the \texttt{GHC.Generics} implementation of |size|, we
see two improvements: (A) we need one less typeclass, namelly |GSize|,
and, (B) the definition is combinator-based. Considering that the
generated \emph{pattern functor} representation of a Haskell datatype
will already be in a \emph{sums-of-products}, we do not lose anything
by enforcing this structure.

  There are still downsides to this approach, as it stands. A notable one being the need
to carry constraints arround: the actual |gsize| written
with the \texttt{generics-sop} library and no sugar looks like:

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

  Introducing information about the recursive positions in a type requires
more expressive codes. In \Cref{sec:explicitsop} our \emph{codes} were 
a list of lists of types, which could be anything. Instead, we
will now have a list of lists of |Atom| to be our codes:

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
in \Cref{sec:konparameter}, we parametrize the whole development.

  Our \emph{codes} here are not polymorphic anymore.
Back in \Cref{sec:explicitsop} we have defined |CodeSOP (Bin
a)|, and this would work for any |a|. This might seen like a
disadvantage at first, but it is in fact quite the opposite. This allows us to
provide a deep conversion for free and relaxes the need to carry
constraints around. Beyond
doubt one needs to have access to the |CodeSOP a| when converting a
|Bin a| to its deep representation. By specifying the types involved
beforehand, we are able to get by without having to carry all of the
constraints we needed in \Cref{sec:explicitsop}. We can benefit
the most from this in the simplicity of combinators we are able to write.


\victor{\huge IM HERE}

  The representation of our codes now requires a functor that map |Atom|s into
Haskell values, that is, |Atom -> *|. The representation |RepFix| is remarkably 
similar to |RepSOP|, but since we now know the recursive positions, we are
able to lift the representation to a functor. In fact, it is a nice exercise to
write the |Functor (RepFix a)| instance. We are using a |newtype| here so
we can partially apply |RepFix|.

\begin{myhs}
\begin{code}
data NA :: * -> Atom -> * where
  NA_I  :: x    -> NA x I
  NA_K  :: Int  -> NA x KInt

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
data Atom  = I Nat | KInt | dots

data Nat   = Z | S Nat
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
  NA_I  :: phi n  -> NA phi (I n)
  NA_K  :: Int    -> NA phi KInt
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
  SZ  ::          -> SNat (P Z)
  SS  ::  SNat n  -> SNat ((P S) n)
\end{code}
\end{myhs}

The limitations of the Haskell type system lead us to introduce |El| as an
intermediate datatype. Our |fromMRec| function does not take one member of
the family directly, but an |El|-wrapped one. However, to construct that value
|El| needs to know its parameters, which amounts to the family we are 
embedding our type into and the index in that family. Those values are not
immediately obvious, but we can use Haskell's |TypeApplications| to work around
it. We shall not go into details about their implementation, but the final
|into| function which injects a value into the corresponding |El| looks like:
\begin{myhs}
\begin{code}
into :: forall fam ty ix dot (ix ~ Idx ty fam , Lkup ix fam ~ ty , IsNat ix) => ty -> El fam ix
into = El
\end{code}
\end{myhs}
where |Idx| is a closed type family implementing the inverse of |Lkup|, that is,
obtaining the index of the type |ty| in the list |fam|. Using this function
we can turn a |rs :: [RoseTree Int]| into its generic representation by writing
|into @RoseTreeFamily rs|. The type application |@RoseTreeFamily| is responsible
for fixing the mutually recursive family we are working with.

  
\paragraph{Deep representation.} In \Cref{sec:explicitfix} we have described a
technique to derive deep representations from shallow representations. We can
play a very similar trick here. The main difference is the definition of the
least fixpoint combinator, which receives an extra parameter of kind |Nat -> *|:
\begin{myhs}
\begin{code}
newtype Fix (codes :: [[[Atom]]]) (ix :: Nat)
  = Fix { unFix :: RepMRec (Fix codes) (Lkup codes ix) }
\end{code}
\end{myhs}
Intuitively, since now we can recurse on different positions, we need to keep
track of the representations for all those positions in the type. This is the
job of the |codes| argument. Furthermore, our |Fix| does not represent a single
datatype, but rather the \emph{whole} family. Thus, we need on each value an
additional index to declare which is the element of the family we are working on.

As in the previous section, we can obtain the deep representation by iteratively
applying the shallow representation. Last time we used |fmap| since the |RepFix|
type was a functor. |RepMRec| on the other hand cannot be given a |Functor|
instance, but we can still define a similar function |mapRec|,
\begin{myhs}
\begin{code}
mapRep :: (forall ix dot phi1 ix -> phi2 ix) -> RepMRec phi2 c -> RepMRec phi2 c
\end{code}
\end{myhs}
This type signature tells us that if we want to change the |phi| argument in 
the representation, we need to provide a function which works over each
possible index this |phi| can take. This makes sense, as |phi| has kind
|Nat -> *|. 
\begin{myhs}
\begin{code}
deepFrom :: Family fam codes => El fam ix -> Fix (RepFix codes ix)
deepFrom = Fix . mapRec deepFrom . from
\end{code}
\end{myhs}

\paragraph{Only well-formed representations are accepted.}
At first glance, it looks like the |Atom| datatype gives too much freedom.
Its |I| constructor receives a natural number, but there is no static check
about this number referring to an actual member of the recursive family we
are describing. For example, the list of codes
|(P [ (P [ (P [ KInt, I (S (S Z))])])])|  is accepted by the compiler
although it does not represent any family of datatypes.

A direct solution to this problem is to introduce yet another index, this
time to the |Atom| datatype, which specifies which indices are allowed.
The |I| constructor is then refined to take not any natural number, but only
those which lie in the range -- this is usually known as |Fin n|.
\begin{myhs}
\begin{code}
data Atom (n :: Nat) = I (Fin n) | KInt | dots
\end{code}
\end{myhs}
Unfortunately 
this approach has a major drawback in Haskell. The lack of dependent types would
require us to turn on the \texttt{-XTypeInType} extension, which although does not
break consistency, can cause the compiler to loop and is generaly seen as an extreme
resort.

By looking a bit more closely, we find that we are not losing any type-safety
by allowing codes which reference an arbitrary number of recursive positions.
Users of our library are allowed to write the previous ill-defined code, but
when trying to write \emph{values} of the representation of that code, the
|Lkup| function detects the out-of-bounds index, raising a type error and
preventing the program from compiling.

\subsection{Parametrized Opaque Types}
\label{sec:konparameter}

Up to this point we have considered |Atom| to include a predetermined selection of
\emph{opaque types}, such as |Int|, each of them represented by one of the
constructors other than |I|. This is far from ideal, for two conflicting reasons:
\begin{enumerate}
\item The choice of opaque types might be too narrow. For example, the user
of our library may decide to use |ByteString| in their datatypes. Since that
type is not covered by |Atom|, nor by our generic approach, this implies that
\texttt{\nameofourlibrary} becomes useless for them.
\item The choice of opaque types might be too wide. If we try to encompass any
possible situation, we might end up with an humongous |Atom| type. But for a
specific use case, we might be interested only in |Int|s and |Float|s, so why
bother ourselves with possibly ill-formed representations and pattern matches
which should never be reached?
\end{enumerate}
The solution is to \emph{parametrize} |Atom|, allowing programmers to choose
which opaque types they want to deal with:
\begin{myhs}
\begin{code}
data Atom kon = I Nat | K kon
\end{code}
\end{myhs}
For example, if we only want to deal with numeric opaque types, we can write:
\begin{myhs}
\begin{code}
data NumericK = KInt | KInteger | KFloat
type NumericAtom = Atom NumericK
\end{code}
\end{myhs}

The representation of codes must be updated to reflect the possibility of
choosing different sets of opaque types. The |NA| datatype provides in this
final implementation just two constructors, one per constructor in |Atom|.
The |NS| and |NP| datatypes do not require any change.
\begin{myhs}
\begin{code}
data NA :: (kon -> *) -> (Nat -> *) -> Atom -> * where
  NA_I  :: phi    n  -> NA kappa phi (I  n)
  NA_K  :: kappa  k  -> NA kappa phi (K  k)

type RepMRec (kappa :: kon -> *) (phi :: Nat -> *) (c :: [[Atom]]) = NS (NP (NA kappa phi)) c
\end{code}
\end{myhs}
The |NA_K| constructor in |NA| makes use of an additional argument |kappa|.
The problem is that we are defining the code for the set of opaque types by
a specific kind, such as |Numeric| above. On the other hand, values which
appear in a field must have a type whose kind is |*|. Thus, we require a mapping
from each of the codes to the actual opaque type they represent, this
is exactly the \emph{opaque type interpretation} |kappa|. Here is the
datatype interpreting |NumericK| into ground types:
\begin{myhs}
\begin{code}
data NumericI :: NumericK -> * where
  IInt      :: Int      -> NumericI KInt
  IInteger  :: Integer  -> NumericI KInteger
  IFloat    :: Float    -> NumericI KFloat
\end{code}
\end{myhs}
The last piece of our framework which has to be updated to support different
sets of opaque types is the |Family| type class. This type class provides an
interesting use case for the new dependent features in Haskell; both |kappa|
and |codes| are parametrized by an implicit argument |kon| which represents
the set of opaque types.
\begin{myhs}
\begin{code}
class Family (kappa :: kon -> *) (fam :: [*]) (codes :: [[[Atom kon]]]) where
  
  fromMRec  :: SNat ix  -> El fam ix -> RepMRec kappa (El fam) (Lkup codes ix)
  toMRec    :: SNat ix  -> RepMRec kappa (El fam) (Lkup codes ix) -> El fam ix
\end{code}
\end{myhs}

All the generic operations implemented in \texttt{\nameofourlibrary} use
parametrized version of |Atom|s and representations described in this section.
For convenience we also provide a basic set of opaque types which includes the
most common primitive Haskell datatypes.

\subsection{Combinators}

  \victor{glue this up; point is: |zip| |map| |elim| and |compos| are the base}

  Through the rest of this section we wish to showcase a selection of particularly
powerful combinators that are remarkably simple to define by exploiting the
\emph{sums-of-products} structure.

For the sake of fostering intuition instead of worrying about
notational overhead, we shall write values of |RepMRec kappa phi c| just like
we would write normal Haskell values. They have the same \emph{sums-of-products} 
structure anyway. Whenever a function is defined
using the |^=| symbol, |C x_1 dots x_n| will stand for a value of the corresponding
|RepMRec phi c|, that is, |There (dots (Here (x_1 :* dots :* x_n :* NP0)))|. 
Since each of these |x_1 dots x_n| might be a recursive type or an opaque type,
whenever we have two functions |f_I| and |f_K| in scope, |fSq x_j| will
denote the application of the correct function for recursive positions, |f_I|,
or opaque types |f_K|. For example, here is the actual code of a function
which applies functions to a |NA| structure:
\begin{myhs}
\begin{code}
bimapNA f_K f_I  (NA_I  i)  = NA_I  (f_I  i)
bimapNA f_K f_I  (NA_K  k)  = NA_K  (f_K  k)
\end{code}
\end{myhs}
and this is how we write the function following this convention:
\begin{myhs}
\begin{code}
bimapNA f_K f_I x ^= f x
\end{code}
\end{myhs}

The first obvious combinator which we can write using the sum-of-products
structure is |map|. 
Our |RepMRec kappa phi c| does not make a regular functor anymore, but a higher
bifunctor. In other words, it requires two functions, one for mapping over
opaque types and other for mapping over |I| positions.

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

%format LambdaTerm = "\HT{Term_{\lambda}}"
\begin{myhs}
\begin{code}
data LambdaTerm  =  Var  String
                 |  Abs  String      LambdaTerm
                 |  App  LambdaTerm  LambdaTerm
\end{code}
\end{myhs}

  The process is conceptually simple. Firstly, for |t_1, t_2 :: LambdaTerm|
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
alphaEq :: LambdaTerm -> LambdaTerm -> Bool
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
note the application of |zipRep|. If two |LambdaTerm|s are made with different
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
over |LambdaTerm|.  If we bring in a more intricate language to the
spotlight, however, manual pattern matching becomes almost untractable
very fast. 

Take the a toy imperative language defined in
\Cref{fig:alphatoy}.
Transporting |alphaEq| from the lambda calculus is fairly simple. For
one, |alhaEq|, |step| and |galphaEq| remain the same.  We just need to
adapt the |go| function. On the other hand, having to write $\alpha$-equivalence
by pattern matching might not be so straight forward anymore. Moreover,
if we decide to change the toy language and add more statements or more expressions,
the changes to the |go| function are minimal, if any. As long as we do not touch
the constructors that |go| patterns matches on, we can use the very same function.

\begin{figure}
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
go StmtP  x = case sop x of
      SAssignP (v_1 :*: v_2) (e_1 :*: e_2)  
         ->  addRule v_1 v_2 >> galphaEq e_1 e_2
      _  ->  step x
go DeclP  x = case sop x of
      DVarP (v_1 :*: v_2) 
         ->  addRule v_1 v_2 >> return True
      DFunP (f_1 :*: f_2) (x_1 :*: x_2) (s_1 :*: s_2)
         ->  addRule f_1 f_2   
         >>  scoped (addRule x_1 x_2 >> galphaEq s_1 s_2)
      _  ->  step x
go ExpP   x = case sop x of
      EVarP (v_1 :*: v_2)
         ->  v_1 =~= v_2
      ECallP (f_1 :*: f_2) (e_1 :*: e_2)
         ->  (&&) <$$> f_1 =~= f_2 <*> galphaEq e_1 e_2 
      _  ->  step x 
go _      x = step x
\end{code}
\end{myhs}
\end{minipage}
\caption{$\alpha$-equality for a toy imperative language}
\label{fig:alphatoy}
\end{figure}

\subsection{The Generic Zipper}

  To conclude our examples section and stress-test our framework, 
we introduce a more complex application of generic programming. 
Zippers~\cite{Huet1997} are a well estabilished technique for 
traversing a recursive datastructure keeping track of the current
\emph{focus point}. Defining generic zippers is nothing new,
this has been done by many authors~\cite{Hinze2004,Adams2010,Yakushev2009}
for many different classes of types in the past. To the best of
the authors knowledge, this is the first definition in a direct
\emph{sums-of-products} style. Moreover, being able to define
the generic zipper in one's generic programming framework is
a non-trivial benchmark to achieve.

  Generally speaking, the zipper keeps track of a focus point in a
datastructure and allows for the user to convinently move this focus
point and to apply functions to whatever is under focus.  This focus
point is expressed by the means of a location type, |Loc|, with a
couple associated functions:

\begin{myhs}
\begin{code}
up      :: Loc a -> Maybe (Loc a)
down    :: Loc a -> Maybe (Loc a)
right   :: Loc a -> Maybe (Loc a)
update  :: (a -> a) -> Loc a -> Loc a
\end{code}
\end{myhs}

  In our case, this location type consists in a distinguished element
of type |ix| and a stack of contexts with a hole of type |ix|, where
we can plug the distinguished element and \emph{leave} the zipper.
All of the following development is parametrized by an interpretation
for opaque types |ki :: kon -> *|, a family |fam :: [*]| and its associated
codes |codes :: [[[Atom kon]]]|; since these are the same for any given family,
let us fix those and ommit them from the declarations to simplify the presentation. 

  A location for the |ix| element of the family, |El fam ix|
is defined by having a distinguished element of the family, possibly of
a different index, |iy| and a stack of contexts that represent a value of
type |El fam ix| with a \emph{hole} of type |El fam iy|.

\begin{myhs}
\begin{code}
data Loc :: Nat -> * where
  Loc :: El fam iy -> Ctxs ix iy -> Loc ix
\end{code}
\end{myhs}

  The stack of contexts represent how deep into the recursive
tree we have descended so far. Each time we unwrap another layer of recursion,
we push some context into the stack to be able to ascend back up. Note how
the |Cons| constructor resembles some sort of composition operation.

\begin{myhs}
\begin{code}
data Ctxs :: Nat -> Nat -> * where
  Nil   :: Ctxs ix ix
  Cons  :: Ctx (Lkup codes iz) iy -> Ctxs ix iz -> Ctxs ix iy
\end{code}
\end{myhs}

  Each individual context, |Ctx c iy| is a choice of a constructor
for the code |c| with a product of the correct type missing an element
of type |El fam iy|, representing the hole where the distinguished element
in |Loc| was supposed to be. 

\begin{myhs}
\begin{code}
data Ctx :: [[Atom kon]] -> Nat -> * where
  Ctx :: Constr n c -> NPHole (Lkup n c) iy -> Ctx c iy

data NPHole :: [Atom kon] -> Nat -> * where
  Here   :: NP (NA ki (El fam)) xs            -> NPHole (I ix  : xs)  ix
  There  :: NA ki (El fam) x -> NPHole xs ix  -> NPHole (x     : xs)  ix
\end{code}
\end{myhs}

  The navigation functions are exactly direct translation of those defined 
for the \texttt{multirec}~\cite{Yakushev2008} library, that use the
|first|, |fill|, and |next| primitives for working over |Ctx|s.
The |fill| is trivial to translate, whereas |first| and |next| require
a slight trick.  We have to wrap the |Nat| parameter of |NPHole| in an
existential in order to manipulate it conveniently:

\begin{myhs}
\begin{code}
data NPHoleE :: [Atom kon] -> * where
  Witness :: El fam ix -> NPHole c ix -> NPHoleE c
\end{code}
\end{myhs}

  Finally, we can define the |firstE| and |nextE| that are used
instead of the |first| and |next| from \texttt{multirec}. The intuition
behind those is pretty simple; |firstE| returns the |NPHole| with the hole
first recursive position (if any) selected, |nextE| tries to find the
next recursive position in a |NPHole|. The |ix| is packed up in an existential
type since we do not really know before hand which member of the mutually
recursive family is seen first in an arbitrary product. These altered
functions have types:

\begin{myhs}
\begin{code}
firstE  :: NP (NA ki (El fam)) xs  -> Maybe (NPHoleE xs)
nextE   :: NPHoleE xs              -> Maybe (NPHoleE xs)
\end{code}
\end{myhs}

  To conclude we can now use flipped compositions for pure functions 
|(>>>) :: (a -> b) -> (b -> c) -> a -> c| and monadic functions
|(>=>) :: (Monad m) => (a -> m b) -> (b -> m c) -> a -> m c| to elegantly
write some \emph{location based} instruction to transform some value
of a |LambdaTerm| (\Cref{sec:alphaequivalence}), for instance.

\begin{minipage}[t]{.55\textwidth}
\begin{myhs}
\begin{code}
tr :: LambdaTerm -> Maybe LambdaTerm
tr = enter  >>>  down 
            >=>  right 
            >=>  update (const $$ Var "c") 
            >>>  leave 
            >>>  return
\end{code}
\end{myhs}
\end{minipage}%
\begin{minipage}[t]{.45\textwidth}
\begin{myhs}
\begin{code}
tr (App (Var "a") (Var "b")) 
  == Just (App (Var "a") (Var "c"))
\end{code}
\end{myhs}
\end{minipage}

  Where |enter| and |leave| witness the isomorphism |El fam ix <-> Loc ix|.

\

There are many other applications for generic programming once mutual recursion
can be accounted. For example, we can diff abstract syntax trees of realistic
languages in a generic fashion~\cite{CacciariMiraldo2017}.

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

\section{Conclusion and Future Work}

In this paper we have presented \texttt{\nameofourlibrary}, a library for
generic programming in Haskell which support both deep and shallow
representations of mutually recursive families of datatypes. We follow the
sums-of-products approach: datatypes are described by a code
consisting of lists (one per datatype) of lists (one per constructor)
of lists (one per field) of atoms. The result is as expressive as other
approaches such as \texttt{multirec}, yet it allows for a more concise
combinator-based approach to defining generic functions.

Future work involves expanding the universe of datatypes that our library
can handle. Currently, every type involved in a recursive family must be
a ground type (of kind |*| in Haskell terms); our Template Haskell derivations
acknowledges this fact by implementing some amount of reduction for types.
This limits the functions we can implement generically, for example we cannot
write a generic |fmap| function, since it operates on types of kind |* -> *|.
\texttt{GHC.Generics} supports type constructors with exactly one argument
via the \texttt{Generic1} type class. We foresee most of the complexity to
be in the definition of |Atom|, as it must support some kind of application
of type constructors to other parameters or opaque types.

The original sum-of-products approach does not handle all the ground types either,
only regular ones~\cite{deVries2014}. We inherit this restriction, and cannot
represent recursive families which involve existentials or GADTs. The problem
in this case is representing the constraints that each constructor imposes
on the type arguments.