\section{Introduction}
\label{sec:introduction}

\emph{(Datatype-)generic programming} provides a mechanism to write functions
by induction on the structure of algebraic datatypes~\cite{Gibbons2006}. 
A well-known example is the |deriving| mechanism
in Haskell, which frees the programmer from writing repetitive functions such as
equality~\cite{haskell2010}. A vast range of approaches are available as
preprocessors, language extensions, or libraries for Haskell~\cite{Rodriguez2008,Magalhaes2012}.
In \Cref{fig:gplibraries} we outline the main design differences between a few
of those libraries.

The core idea underlying generic programming is the fact that a great
number of datatypes can be described in a uniform fashion.
Consider the following datatype representing binary trees with data stored in their
leaves:
\begin{myhs}
\begin{code}
data Bin a = Leaf a | Bin (Bin a) (Bin a)
\end{code}
\end{myhs}
A value of type |Bin a| consists of a choice between two constructors.
For the first choice, it also contains a value of type |a| whereas 
for the second if contains two subtrees as children. This means that the |Bin a| type
is isomorphic to |Either a (Bin a , Bin a)|. 

Different libraries differ on how they define their underlying generic descriptions. 
For example,
\texttt{GHC.Generics}~\cite{Magalhaes2010} defines the representation of |Bin|
as the following datatype:

\begin{myhs}
\begin{code}
Rep (Bin a) = K1 R a :+: (K1 R (Bin a) :*: K1 R (Bin a))
\end{code}
\end{myhs}

which is a direct translation of |Either a (Bin a , Bin a)|, but using
the combinators provided by \texttt{GHC.Generics}, namely |:+:| and
|:*:|. In addition, we need two conversion functions |from :: a -> Rep
a| and |to :: Rep a -> a| which form an isomorphism between |Bin a|
and |Rep (Bin a) x|.  All this information is tied to the original
datatype using a type class:

\begin{myhs}
\begin{code}
class Generic a where
  type Rep a :: Star
  from  :: a      -> Rep a 
  to    :: Rep a  -> a
\end{code}
\end{myhs}
  Most generic programming libraries follow a similar pattern of
defining the \emph{description} of a datatype in the provided uniform
language by some type level information, and two functions witnessing
an isomorphism. A important feature of such library is how this
description is encoded and which are the primitive operations for
constructing such encodings, as we shall explore in
\Cref{sec:designspace}.

  In \Cref{fig:gplibraries} we show a small comparison of some of the
design decisions took by existing libraries and place our work within
those parameters. The \emph{dynamic} column contains the
libraries~\cite{Lammel2003,Mitchell2007} that provide generic
functionality by the means of the |Data| and |Typeable| type classes,
and consist in a completely different strand of work from ours. On the
other hand, the \emph{static} column lists the libraries that provide
type level descriptions of the generic datatypes, and this is what we
focus on.

  Static generic programming libraries rely on type level information
to provide their generic functionality. In more permissive
\emph{pattern functor} approach we have
\texttt{GHC.Generics}~\cite{Magalhaes2010}, being the most commonly
used one, that effectively replaced \texttt{regular}~\cite{Noort2008}.
The former only allows for a \emph{shallow} representation whereas the
later allows for both \emph{deep} and \emph{shallow} representations
by maintaining information about the recursive occurences of a
type. Oftentimes though, one actually needs more than one recursive
type, justifying the need to \texttt{multirec}~\cite{Yakushev2009}.
These libraries are too permissive though, for instance, |U1 :*: Maybe|
is a perfectly valid \texttt{GHC.Generics} \emph{pattern functor} but
will break generic functions.  The way to fix this is to ensure that the
\emph{pattern functors} abide by a certain format. That is, define the
\emph{pattern functors} by induction on some \emph{Code}, that can be
inspected and pattern matched on. This is the approach of
\texttt{generics-sop}~\cite{deVries2014}. The more restrictire
\emph{Code} approach allows one to write concise, combinator-based,
generic programs. The novelty in our work is in the intersection of
both the expressivity of \texttt{multirec}, allowing the encoding of
mutually recursive families, with the convenience of the more modern
\texttt{generics-sop}~\cite{deVries2014} style.

\begin{figure}\centering
\ra{1.3}
\begin{tabular}{@@{}llll@@{}}\toprule
                   & Dynamic             & \multicolumn{2}{c}{Static} \\ \cmidrule{3-4}
                   &                     & Pattern Functors      & Codes \\ \midrule
  Simple Recursion & \texttt{SYB}        & \texttt{GHC.Generics} & \texttt{generics-sop} \\
                   & \texttt{uniplate}   & \texttt{regular}      &  \\
  Mutual Recursion & \texttt{multiplate} & \texttt{multirec}     & \textbf{\texttt{\nameofourlibrary}} \\
\bottomrule
\end{tabular}
\caption{Spectrum of Generic Programming Libraries}
\label{fig:gplibraries}
\end{figure}

\subsection{Contributions}

In this paper we make the following contributions:
\begin{itemize}
\item We extend the sum-of-products approach of \citet{deVries2014} to 
care for recursion (\Cref{sec:explicitfix}), allowing for \emph{shallow} and
\emph{deep} representations. We proceed generalizing even further to mutually 
recursive families of datatypes (\Cref{sec:family}).
\item We illustrate the use of our library on familiar examples
such as equality, $\alpha$-equivalence and the zipper (\Cref{sec:mrecexamples}),
illustrating how it supersedes the previous approaches.
\item We provide Template Haskell functionality to derive all the
boilerplate code needed to use our library (\Cref{sec:templatehaskell}).
The novelty lies in our handling of instantiated type constructors.
\end{itemize}
We have packaged our results as a Haskell library, \texttt{\nameofourlibrary},
which is being delivered as suplementary material. 

\subsection{Design Space}
\label{sec:designspace}

\paragraph{Deep versus shallow.}
There are two ways to represent a generic value. When using a
\emph{shallow} representation only one layer of the value is turned
into a generic form by a call to |from|.  This is the kind of
representation we get from \texttt{GHC.Generics}, among others.

The other side of the spectrum is the \emph{deep} representation, in
which the entire value is turned into the representation that the
generic library provides in one go. In a deep representation, the
positions where recursion takes place are marked explicitly. This
additional power has been used, for example, to define regular
expressions over Haskell datatypes~\cite{Serrano2016}.  Depending on
the use case, a shallow representation might be more efficient if only
part of the value needs to be inspected. On the other hand, deep
representations are sometimes easier to use, since the conversion is
performed in one go.

In general, descriptions that support a deep representation are more
involved than those that support only a shallow representation. The
reason is that the \emph{recursive} positions in your datatype must be
marked explicitly. In the |Bin| example, the description of the |Bin|
constructor changes from ``this constructors has two fields of the
|Bin a| type'' to ``this constructor has two fields in which you
recurse''. Therefore, a \emph{deep} encoding requires some
a \emph{least fixpoint} combinator. The \texttt{regular}
library~\cite{Noort2008}, for instance, is based on this feature.

\paragraph{Sum of Products}

Most generic programming libraries build their type level descriptions out of three basic
combinators: (1) \emph{constants}, which indicate a type which should appear
as-is; (2) \emph{products} (usually written as |:*:|) which are used to
build tuples; and (3) \emph{sums} (usually written as |:+:|) which
encode the choice between constructors. |Rep (Bin a)| above is expressed in
this form. Note, however, that there is no restriction on \emph{how} these
can be combined. 

In practice, one can always use a sum of products to represent a datatype -- a sum
to express the choice of constructor, and within each constructor a product to
declare which fields you have. A recent approach to generic programming~\cite{deVries2014}
explicitly uses a list of lists of types, the outer one representing the sum
and each inner one thought as products. The $\HS{'}$ sign in the code below marks the
list as operating at the type level, as opposed to term-level lists which exists
at run-time. This is an example of Haskell's \emph{datatype} promotion~
\cite{Yorgey2012}.
\begin{myhs}
\begin{code}
CodeSOP (Bin a) = P [ P [a], P [Bin a, Bin a] ]
\end{code}
\end{myhs}
The shape of this description follows more closely the shape of Haskell datatypes, and
make it easier to implement generic functionality.

  Note how the \emph{codes} are different than the \emph{representation}.
The later being defined by induction on the former.
This is quite a subtle point and it is common to see both
terms being used interchangeably.  Here, the \emph{representation} is
mapping the \emph{codes}, of kind |P [ P [ Star ] ]|, into |Star|. The
\emph{code} can be seen as the format that the \emph{representation}
must adhere to. Previously, in the pattern functor approach, the
\emph{representation} was not guaranteed to have a certain
structure. The expressivity of the language of \emph{codes} is
proportional to the expressivity of the combinators the library can
provide. 

\paragraph{Mutually recursive datatypes.}

We have described several axes taken by different approaches to generic
programming in Haskell. Unfortunately, most of the approaches restrict themselves
to \emph{regular} types, in which recursion always goes into the \emph{same}
datatype, which is the one being defined. This is not enough for some practical applications. 
The syntax of many programming languages is expressed naturally using
a mutually recursive family. Consider Haskell itself, one of the 
possibilities of an expression is to be a |do| block, while a |do| block itself is
composed by a list of statements which may include expressions.
\begin{myhs}
\begin{code}
data Expr  = ... | Do [Stmt] | ...
data Stmt  = Assign Var Expr | Let Var Expr
\end{code}
\end{myhs}

Another example is found in HTML and XML documents. 
They are better described by a Rose tree, 
which can be described by this family of datatypes\footnote{%
It can actually be proved that |Rose a| is isomorphic to a regular
datatype.}:
\begin{myhs}
\begin{code}
data Rose  a  =  a :>: [Rose a]
data []    a  =  [] | a : [a]
\end{code}
\end{myhs}
The mutual recursion becomes apparent once one instantiaties |a| to some
ground type, for instance:
\begin{myhs}
\begin{code}
data RoseI  =  Int :>: ListI
data ListI  =  Nil | RoseI : ListI
\end{code}
\end{myhs}

The \texttt{multirec} library~\cite{Yakushev2009} is a generalization of
\texttt{regular} which handles mutually recursive families. From \texttt{regular}
it inherits the approach using representations. 
The motivation of our work stems from the desire of having the concise structure
that \emph{codes} give to the \emph{representations}, together with the 
information for recursive positions in a mutually recursive setting.

\paragraph{Deriving the representation.}

Generic programming alleviates the problem of repetitively writing operations
such as equality or pretty-printing, which depend on the structure of the
datatype. But in order to do so, they still require the programmer to figure
out the right description and write conversion function |from| and |to| that type. This is
tedious, and also follows the shape of the type!

For that reason, most generic programming libraries also include some
automatic way of generating this boilerplate code. \texttt{GHC.Generics} is
embedded in the compiler; most others use Template Haskell~\cite{Sheard2002},
the meta-programming facility found in GHC. In the former case, programmers
write:
\begin{myhs}
\begin{code}
data Bin a = ... deriving Generic
\end{code}
\end{myhs}
to open the doors to generic functionality.

There is an interesting problem that arises when we have mutually recursive
datatypes and want to automatically generate descriptions.
The definition of |Rose a| above uses the list type, but not
simply |[a]| for any element type |a|, but the specific instance |[Rose a]|. This means that the
procedure to derive the code must take this fact into account.
Shallow descriptions do not suffer too much from this problem. For deep
approaches, though, how to solve this problem is key to derive a useful
description of the datatype.

\section{Background}
\label{sec:genericprog}

  Before diving head first into our generic programming framework,
let us take a tour of the existing generic programming libraries. For that,
will be looking at a generic |size| function from a few different angles,
illustrating how different techniques relate and the nuances between them.
This will let us gradually build up to our framework, that borrows 
pieces of each of the different approaches, and combines them without compromise.

\subsection{GHC Generics}
\label{sec:patternfunctors}

  Since version $7.2$, GHC supports some basic, off the shelf, generic
programming using \texttt{GHC.Generics}~\cite{Magalhaes2010}, 
which exposes the \emph{pattern functor} of a datatype. This
allows one to define a function for a datatype by induction
on the structure of its (shallow) representation using \emph{pattern functors}.

  These \emph{pattern functors} are parametrized versions of tuples,
sum types (|Either| in Haskell lingo), and unit, empty and constant
functors. These provide a unified view over data: the generic
\emph{representation} of values.  The values of a suitable type |a|
are translated to this representation by the means of the function
|fromGen :: a -> RepGen a|. Note that the subscripts are there 
solely to disambiguate names that appear in many libraries. Hence,
|fromGen| is, in fact, |GHC.Generics.from|.

  Defining a generic function is done in two
steps. First, we define a class that exposes the function
for arbitrary types, in our case, |size|.

\begin{myhs}
\begin{code}
class Size (a :: Star) where
  size :: a -> Int
\end{code}
\end{myhs}

  We provide an instance for |Bin a|:

\begin{myhs}
\begin{code}
instance (Size a) => Size (Bin a) where
  size = gsize . fromGen
\end{code}
\end{myhs}

  The |gsize| function, that operates on the representation of
datatypes, is the second piece we need to define. We use another class
and the instance mechanism to encode a definition by induction on
representations.  Here, they are \emph{pattern functors}.

\begin{myhs}
\begin{code}
class GSize (rep :: Star -> Star) where
  gsize :: rep x -> Int
instance (GSize f , GSize g) => GSize (f :*: g) where
  gsize (f :*: g) = gsize f + gsize g
instance (GSize f , GSize g) => GSize (f :+: g) where
  gsize (L1 f) = gsize f
  gsize (R1 g) = gsize g
\end{code}
\end{myhs}

  We still have to handle the cases were 
we might have an arbitrary type in a position, modeled by the
constant functor. We must require an instance of |Size|
so we can successfully tie the recursive knot.

\begin{myhs}
\begin{code}
instance (Size x) => GSize (K1 R x) where
  gsize (K1 x) = size x
\end{code}
\end{myhs}

  This technique of \emph{mutually recursive classes} is quite 
specific to \texttt{GHC.Generics} flavor of generic programming.
\Cref{fig:sizederiv} illustrates how the compiler go about choosing
instances for computing |size (Bin (Leaf 1) (Leaf 2))|.

\begin{figure}\centering
\begin{align*}
  |size (Bin (Leaf 1) (Leaf 2))| 
    &= |gsize (fromGen (Bin (Leaf 1) (Leaf 2)))| \\
    &= |gsize (R1 (K1 (Leaf 1) :*: K1 (Leaf 2)))| \\
    &= |gsize (K1 (Leaf 1)) + gsize (K1 (Leaf 2))| \\
    &= |size (Leaf 1) + size (Leaf 2)| \tag{$\dagger$}\\
    &= |gsize (fromGen (Leaf 1)) + gsize (fromGen (Leaf 2))|\\
    &= |gsize (L1 (K1 1)) + gsize (L1 (K1 2))|\\
    &= |size (1 :: Int) + size (2 :: Int)|   
\end{align*}
\caption{Reduction of |size (Bin (Leaf 1) (Leaf 2))|}
\label{fig:sizederiv}
\end{figure}

  Finally, we would just need an instance for |Size Int| to compute
the final result. Theless, the literals of type |Int| illustrate
what we call \emph{opaque types}: those types that constitute the base
of the universe and are \emph{opaque} to the representation language.

  In practice, one usually applies yet another maneuver to make this
process more convenient. Note that the implementation of |size| for
|Bin a| relies on the implementation of |gsize|, after converting a |Bin a|
to its generic representation. We can instruct GHC to do this automatically
using \texttt{-XDefaultSignatures} and modifying the |Size| class to:

\begin{myhs}
\begin{code}
class Size (a :: Star) where
  size :: a -> Int
  default size  :: (GenericGen a , GSize (RepGen a))
                => a -> Int
  size = gsize . fromGen
\end{code}
\end{myhs}

  The |default| keyword instructs Haskell to use the provided
implementation whenever none is provided and the constraint |(GenericGen a , GSize (RepGen a))| 
can be satisfied when declaring an instance for |Size a|. 

  One interesting aspect we should note here is the clearly
\emph{shallow} encoding that |from| provides. That is, we only
represent \emph{one layer} at a time. For example, take the step
$(\dagger)$ in \Cref{fig:sizederiv}: after unwrapping the calculation
of the first \emph{layer}, we are back to having to calculate |size|
for |Bin Int|, not their generic representation.

  Upon reflecting on the generic |size| function above, we see a
number of issues. Most notably is the amount of boilerplate to achieve
a conceptually simple task: sum up all the sizes of the fields of
whichever constructors make up the value. This is a direct consequence
of not having access to the \emph{sum-of-products} structure that
Haskell's |data| declarations follow.  A second issue is that the
generic representation does not carry any information about the
recursive structure of the type.  Instead, we are relying on the
instance search mechanism to figure out that the recursive arguments
can be consumed with the |default size| function. The
\texttt{regular}~\cite{Noort2008} library addresses this issue by
having a specific \emph{pattern functor} for recursive positions.

  Perhaps even more subtle, but also more worrying, is that we have no
guarantees that the |RepGen a| of a type |a| will be defined using
only the supported \emph{pattern functors}. Fixing this would require
one to pin down a single language for representations, that is,
the \emph{code} of the datatype. Besides correctness issues, the
having \emph{codes} greatly improves the definition of \emph{ad-hoc} 
generic combinators. Every generic function has to follow the
\emph{mutually recursive classes} technique we shown.

\subsection{Explicit Sums of Products}
\label{sec:explicitsop}

  We will now examine the approach used by the \texttt{generics-sop}~\cite{deVries2014}
library. The main difference is in the introduction of \emph{Codes},
that limit the structure of representations.

  Had we had access to a representation of the \emph{sum-of-products}
structure of |Bin|, we could have defined our |gsize| function following
a informal description: sum up the sizes of the fields inside a value,
ignoring the constructor.

  Unlike \texttt{GHC.Generics}, the representation of values is
defined by induction on the \emph{code} of a datatype, this \emph{code}
is a type level list of lists of kind |Star|, whose semantics is
consonant to a formula in disjunctive normal form.  The outer list is
interpreted as a sum and the each of the inner lists as a product.
This section provides an overview of \texttt{generic-sop} as required
to understand our techniques, we refer the reader to the original
paper~\cite{deVries2014} for a more comprehensive explanation.

  Using a \emph{sum-of-products} approach one could write the |gsize|
function as easily as:

\begin{myhs}
\begin{code}
gsize :: (GenericSOP a) => a -> Int
gsize  = sum . elim (map size) . fromSOP
\end{code}
\end{myhs}

  Ignoring the details of |gsize| for a moment, let us focus just on
its high level structure. Remembering that |from| now returns a
\emph{sum-of-products} view over the data, we are using an eliminator,
|elim|, to apply a function to the fields of the constructor used to
create a value of type |a|. This eliminator then applies |map size| to
the fields of the constructor, returning something akin to a
|[Int]|. We then |sum| them up to obtain the final size.

  The generic codes consist of a type level list of lists. The outer
list represents the constructors of a type, and will be interpreted as
a sum, whereas the inner lists are interpreted as the fields of the
respective constructors, interpreted as products.

\begin{myhs}
\begin{code}
type family    CodeSOP (a :: Star) :: P ([ (P [Star]) ])

type instance  CodeSOP (Bin a) = P ([ P [a] , P ([Bin a , Bin a]) ])
\end{code}
\end{myhs}

  The \emph{representation} is then defined by induction on
|CodeSOP| by the means of generalized $n$-ary sums, |NS|, and $n$-ary products,
|NP|. With a slight abuse of notation, one can view |NS| and |NP|
through the lens of the following isomorphisms:
\begin{align*}
  | NS f [k_1 , k_2 , dots]| &\equiv |f k_1 :+: (f k_2 :+: dots)| \\
  | NP f [k_1 , k_2 , dots]| &\equiv |f k_1 :*: (f k_2 :*: dots)| 
\end{align*}

  We could then define the representation |RepSOP| to be
|NS (NP (K1 R))|, echoing the isomorphisms above, where |data K1 R a = K1 a| 
is borrowed from \texttt{GHC.Generics}. Note that we already
need the parameter |f| to pass |NP| to |NS| here. 
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
scratch using \emph{GADTs}~\cite{Xi2003}.
By pattern matching on the values of |NS| and |NP| we
inform the type checker of the structure of |CodeSOP|.

\begin{minipage}[t]{.45\textwidth}
\begin{myhs}
\begin{code}
data NS :: (k -> Star) -> [k] -> Star where
  Here   :: f k      -> NS f (k (P (:)) ks)
  There  :: NS f ks  -> NS f (k (P (:)) ks)
\end{code}
\end{myhs}
\end{minipage}\begin{minipage}[t]{.45\textwidth}
\begin{myhs}
\begin{code}
data NP :: (k -> Star) -> [k] -> Star where
  NP0  ::                    NP f (P [])
  :*   :: f x -> NP f xs ->  NP f (x (P (:)) xs)
\end{code}
\end{myhs}
\end{minipage}

  Finally, since our atoms are of kind |Star|, we can use the identity
functor, |I|, to interpret those and define the final representation
of values of a type |a| under the \emph{SOP} view:

\begin{myhs}
\begin{code}
type RepSOP a = NS (NP I) (CodeSOP a)

newtype I (a :: Star) = I { unI :: a }
\end{code}
\end{myhs}

  To support the claim that one can define general combinators for
working with these representations, let us look at |elim| and |map|,
used to implement the |gsize| function in the beginning of the section.

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

  Reflecting on the current definition of |size|, especially in
comparison to the \texttt{GHC.Generics} implementation of |size|, we
see two improvements: (A) we need one fewer type class, namely |GSize|,
and, (B) the definition is combinator-based. Considering that the
generated \emph{pattern functor} representation of a Haskell datatype
will already be in a \emph{sums-of-products}, we do not lose anything
by enforcing this structure.

  As it stands, There are still downsides to this approach. A notable
one is the need to carry constraints around: the actual |gsize|
written with the \texttt{generics-sop} library and no sugar looks
like:

\begin{myhs}
\begin{code}
gsize :: (Generic a , All2 Size (CodeSOP a)) => a -> Int
gsize = sum . hcollapse . hcmap (Proxy :: Proxy Size) (mapIK size) . fromSOP
\end{code}
\end{myhs}

  The |All2 Size (CodeSOP a)| constraint tells the compiler that
all of the types serving as atoms for |CodeSOP a| are an instance of |Size|.
In our case, |All2 Size (CodeSOP (Bin a))| expands to |(Size a , Size (Bin a))|.
The |Size| constraint also has to be passed around with a |Proxy| for
the eliminator of the $n$-ary sum. This is a direct consequence of a
\emph{shallow} encoding: since we only unfold one layer of recursion
at a time, we have to carry proofs that the recursive arguments can
also be translated to a generic representation. We can relieve this
burden by recording, explicitly, which fields of a constructor are
recursive or not.

\section{Explicit Fix: Deep and Shallow for free}
\label{sec:explicitfix}

  In this section we will start to look at our approach, essentially
combining the techniques from the \texttt{regular} and \texttt{generics-sop}
libraries. Later we extend the constructions to handle mutually recursive
families instead of simple recursion.

  Introducing information about the recursive positions in a type
requires more expressive codes then in \Cref{sec:explicitsop}, where
our \emph{codes} were a list of lists of types, which could be
anything. Instead, we will now have a list of lists of |Atom| to be
our codes:

\begin{myhs}
\begin{code}
data Atom = I | KInt | dots

type family    CodeFix (a :: Star)   ::  P [ P [Atom] ]

type instance  CodeFix (Bin Int)  =   P [ P [KInt] , P [I , I] ]
\end{code}
\end{myhs}

  Where |I| is used to mark the recursive positions and |KInt, dots|
are codes for a predetermined selection of primitive types, which we
refer to as \emph{opaque types}.
Favoring the simplicity of the presentation, we will stick with only
hard coded |Int| as the only opaque type in the universe. Later on,
in \Cref{sec:konparameter}, we parametrize the whole development
by the choice of opaque types.

  We can no longer represent polymorphic types types in this universe
-- the \emph{codes} themselves are not polymorphic.  Back in
\Cref{sec:explicitsop} we have defined |CodeSOP (Bin a)|, and this
would work for any |a|. This might seen like a disadvantage at first,
but it is in fact quite the opposite. This allows us to provide a deep
conversion for free and relaxes the need to carry constraints
around. Beyond doubt one needs to have access to the |CodeSOP a| when
converting a |Bin a| to its deep representation. By specifying the
types involved beforehand, we are able to get by without having to
carry all of the constraints we needed, for instance, for |gsize| at
the end of \Cref{sec:explicitsop}.  We can benefit the most from this
in the simplicity of combinators we are able to write.

  Wrapping our |toFix| and |fromFix| isomorphism into a type class and writing the
instance that witnesses that |Bin Int| has a |CodeFix| and is isomorphic
to its representation is quite straight forward.

\begin{myhs}
\begin{code}
class GenericFix a where
  fromFix  :: a -> RepFix a a
  toFix    :: RepFix a a -> a
\end{code}
\end{myhs}

\begin{myhs}
\begin{code}
instance GenericFix (Bin Int) where
  fromFix (Leaf x)   = Rep (        Here  (NA_K x  :* NP0))
  fromFix (Bin l r)  = Rep (There ( Here  (NA_I l  :* NA_I r :* NP0)))
\end{code}
\end{myhs}

  We just need to define a way to map an |Atom| into |Star|.
Since an atom can be either an opaque type, known statically, or some other
type that will be used as a recursive position later on, we simply receive
it as another parameter. Hence:

\begin{myhs}
\begin{code}
data NA :: Star -> Atom -> Star where
  NA_I  :: x    -> NA x I
  NA_K  :: Int  -> NA x KInt

newtype RepFix a x = Rep { unRep :: NS (NP (NA x)) (Code a) }
\end{code}
\end{myhs}

  It is a interesting exercise to implement the |Functor (RepFix a)| instance.
We were only able to lift it to a functor by recording the information about
the recursive positions. Otherwise, there would be no way to know where to apply |f|
when defining |fmap f|.

  Nevertheless, working directly with |RepFix| is hard -- we need
to pattern match on |There| and |Here|, whereas we actually want to
have the notion of \emph{constructor} generically too! 
The main advantage of the \emph{sum-of-products} structure is to allow
a user to pattern match on generic representations just like they would
on values of the original type, constrasting eith \texttt{GHC.Generics}. One 
can precisely state that a value of a representation is composed of a
choice of constructor and its respective product of fields. The
|View| type below exposes this very structure, where |Constr n sum| is
a proof that |n| is a valid constructor for |sum|, essentially saying
|n < length sum|. The |Lkup| is just a type level list
lookup, we will come back it in more details in \Cref{sec:family}.

\begin{myhs}
\begin{code}
data View :: [[ Atom ]] -> Star -> Star where
  Tag :: Constr n sum -> NP (NA x) (Lkup sum n) -> View sum x
\end{code}
\end{myhs}

  Where |Constr| and |Lkup| are defined as:

%\begin{minipage}[t]{.45\textwidth}
\begin{myhs}
\begin{code}
data Constr :: Nat -> [k] -> Star where
  CZ  ::              -> Constr Z      (x : xs)
  CS  :: Constr n xs  -> Constr (S n)  (x : xs)
\end{code}
\end{myhs}

%\end{minipage}
%\begin{minipage}[t]{.45\textwidth}
\begin{myhs}
\begin{code}
type family Lkup (ls :: [k]) (n :: Nat) :: k where
  Lkup (P [])    _          = TypeError "Index out of bounds"
  Lkup (x : xs)  (P Z)      = x
  Lkup (x : xs)  ((P S) n)  = Lkup xs n
\end{code}
\end{myhs}
%\end{minipage}

  In order to improve type error messages, we generate a |TypeError| whenever we
reach the given index |n| is out of bounds. Interestingly, our design
guarantees that this case is never reached by the definition of |Constr|.

  The real convenience comes from being able to easily pattern
match and inject into and from generic values. 
Unfortunately, matching on |Tag| requires describing in full detail
the shape of the generic value using the elements of |Constr|.
Using pattern synonyms~\cite{Pickering2016} we can define
those patterns once and for all, and give them more descriptive names.
For example, here are the synonyms describing
the constructors |Bin| and |Leaf| as |View (Code (Bin Int)) x|:
\footnote{Throughout this paper we use the syntax |(Pat C)| 
to refer to the pattern describing a view for constructor |C|.}

\begin{myhs}
\begin{code}
pattern (Pat Leaf)  x    = Tag CZ       (NA_K x :* NP0)
pattern (Pat Bin)   l r  = Tag (CS CZ)  (NA_I l :* NA_I r :* NP0)
\end{code}
\end{myhs}

The functions that perform the pattern matching and injection are the
|inj| and |sop| below.

\begin{myhs}
\begin{code}
inj  :: View    sum  x  -> RepFix  sum  x
sop  :: RepFix  sum  x  -> View    sum  x
\end{code}
\end{myhs}

  We illustrate the use of |sop| and |inj| by the |mirror| function,
that behaves as the identity on leaves but swaps the left and right subtree
of every |Bin| node.

\begin{myhs}
\begin{code}
mirror :: RepFix (Bin Int) (Bin Int) -> RepFix (Bin Int) (Bin Int)
mirror x = case sop of
             (Pat Bin) l r -> inj $ (Pat Bin) (mirror (from l)) (mirror (from r))
             (Pat Leaf) x  -> inj $ (Pat Leaf) x
\end{code}
\end{myhs}

  As we have seen, patterns for every constructor of a datatype as a |View|
are very useful for the style of generic programming using sums-of-products.
The Template Haskell functionality in \texttt{\nameofourlibrary} generates
them as part of the derivation of generic functionality.

  Having the core of the \emph{sums-of-products} universe defined,
we can turn our attention to writing the combinators that the programmer
will use. These will be defined by induction on the |CodeFix| instead of
having to rely on instances, like in \Cref{sec:patternfunctors}. 
For instance, lets look at |compos|, which applies a function |f| everywhere 
on the recursive structure.

\begin{myhs}
\begin{code}
compos :: (GenericFix a) => (a -> a) -> a -> a
compos f = toFix . fmap f . fromFix
\end{code}
\end{myhs}

  Although more interesting in the mutually recursive setting,
\Cref{sec:family}, we can illustrate its use for traversing a
tree and adding one to its leaves\footnote{%
This is, in fact, just a very convoluted way
writing |fmap (+1) :: Bin Int -> Bin Int|}.

\begin{myhs}
\begin{code}
example :: Bin Int -> Bin Int
example (Leaf n)  = Leaf (n + 1)
example x         = compos example x
\end{code}
\end{myhs}

  It is worth nothing the \emph{catch-all} case, allowing one to
focus only on the interesting patterns and using a default implementation
everywhere else.
  
\paragraph{Converting to a deep representation.}  Our |fromFix|
still returns a shallow representation. But by constructing the least
fixpoint of |RepFix a| we can easily obtain the deep encoding for
free, by simply recursively translating each layer of the shallow
encoding.

\begin{myhs}
\begin{code}
newtype Fix f = Fix { unFix :: f (Fix f) }

deepFrom :: (GenericFix a) => a -> Fix (RepFix a)
deepFrom = Fix . fmap deepFrom . fromFix
\end{code}
\end{myhs}

  So far, we are handling the same class of types
as the \texttt{regular}~\cite{Noort2008} library, but we are imposing 
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

  Sometimes we actually want to consume a value and produce
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

  Finally, we come full circle to our running |gsize| example
as it was promised in the introduction. Noticeably the simplest
implementation so far.

\begin{myhs}
\begin{code}
gsize :: (Generic a) => a -> Int
gsize = crush (const 1) sum
\end{code}
\end{myhs}

  Let us take a step back and reflect upon the current setting we have
so far achieved. We have combined the insight from
the \texttt{regular} library of keeping track of recursive positions
with the convenience for the \texttt{generics-sop} for enforcing a
specific \emph{normal form} to representations. By doing so, we were
able to provide a \emph{deep} encoding for free. Essentially freeing
us from the burden of maintaining complicated constraints needed for
handling the types within the topmost constructor. The information
about the recursive position allows us to write neat combinators like
|crush| and |compos| together with a convenient |View| type for
keeping a choice of constructor handy. The only thing keeping us from
handling real life applications is the limited form of recursion. When
a user requires a generic programming library, chances are they need
to traverse and consume mutually recursive structures.

\section{Mutual Recursion}
\label{sec:family}

  Conceptually, going from regular types (\Cref{sec:explicitfix}) to
mutually recursive families is simple. We just need to be able to reference
not only one type variable, but one for each element in the family.
As a running example, we use the \emph{rose tree} family from the
introduction.
\begin{myhs}
\begin{code}
data Rose  a  =  a :>: [Rose a]
data []    a  =  [] | a : [a]
\end{code}
\end{myhs}

The previously introduced |CodeFix| is not expressive enough to
describe this datatype. In particular, when we try to write
|CodeFix (Rose Int)|, there is no immediately recursive appearance of
|Rose| itself, so we cannot use the atom |I| in that position. Furthermore
|[Rose a]| is not an opaque type either, so we cannot
use any of the other combinators provided by |Atom|. We would
like to record information about |[Rose Int]| referring to itself via another datatype.

Our solution is to move from codes of datatypes to \emph{codes for families of
datatypes}. We no longer talk about |CodeFix (Rose Int)| or
|CodeFix [Rose Int]| in isolation. Codes only make sense
within a family, that is, a list of types. Hence, we talk about
|CodeMRec (P [Rose Int,  [Rose Int]])|. That is, the codes of the
two types in the family. Then we extend the language
of |Atom|s by appending to |I| a natural number which specifies 
the member of the family to recurse:
\begin{myhs}
\begin{code}
data Atom  = I Nat | KInt | dots

data Nat   = Z | S Nat
\end{code}
\end{myhs}
The code of this recursive family of datatypes can be finally described as:
\begin{myhs}
\begin{code}
type FamRose           = P [Rose Int, [Rose Int]]

type CodeMRec FamRose  = (P  [ (P [ (P [ KInt, I (S Z)])])          -- code for Rose Int
                             , (P [ (P []), P [ I Z, I (S Z)]])])   -- code for [Rose Int]
\end{code}
\end{myhs}
Let us have a closer look at the code for |Rose Int|, which appears in the
first place in the list. There is only one constructor which has an |Int| field,
represented by |KInt|, and another in which we recur to the second member of 
our family (since lists are 0-indexed, we represent this by |S Z|). Similarly,
the second constructor of |[Rose Int]| points back to both |Rose Int|
using |I Z| and to |[Rose Int]| itself via |I (S Z)|.

  Having settled on the definition of |Atom|, we now need to adapt |NA| to
the new |Atom|s. In order to interpret any |Atom| into |Star|, we now need
a way to interpret the different recursive positions. This information is given
by an additional type parameter |phi| from natural numbers into types.
\begin{myhs}
\begin{code}
data NA :: (Nat -> Star) -> Atom -> Star where
  NA_I  :: phi n  -> NA phi (I n)
  NA_K  :: Int    -> NA phi KInt
\end{code}
\end{myhs}
The additional |phi| naturally bubbles up to the representation of codes.
\begin{myhs}
\begin{code}
type RepMRec (phi :: Nat -> Star) (c :: [[Atom]]) = NS (NP (NA phi)) c
\end{code}
\end{myhs}
The only missing piece is tying the recursive loop here. If we want our
representation to describe a family of datatypes, the obvious choice
for |phi| is to look a type up at |FamRose|. In fact,
we are just performing a type level lookup in the family.
Recall the definition of |Lkup| from \Cref{sec:explicitfix}: 
\begin{myhs}
\begin{code}
type family Lkup (ls :: [k]) (n :: Nat) :: k where
  Lkup (P [])    _          = TypeError "Index out of bounds"
  Lkup (x : xs)  (P Z)      = x
  Lkup (x : xs)  ((P S) n)  = Lkup xs n
\end{code}
\end{myhs}

In principle, this is enough to provide a ground representation for the family
of types. Let |fam| be the family of ground types, like
|(P [Rose Int, [Rose Int]])|, and |codes| the corresponding list
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
gives us a \emph{shallow} representation. As an example, below is the expansion
for index 0 of the rose tree family. Note how it is isomorphic to the representation
that \texttt{GHC.Generics} would have chosen.
\begin{myhs}
\begin{code}
 RepMRec  (Lkup FamRose) (Lkup (CodeMRec FamRose) Z)
  =    RepMRec  (Lkup FamRose)      (P [ (P [ KInt, I (S Z)])])
  =    NS (NP (NA (Lkup FamRose)))  (P [ (P [ KInt, I (S Z)])])
  ==   K1 R Int :*: K1 R (Lkup FamRose (S Z))
  =    K1 R Int :*: K1 R [Rose Int]
\end{code}
\end{myhs}

Unfortunately, Haskell only allows saturated, that is, fully-applied type
families. Hence, we cannot partially apply |Lkup| like we did it in the example above.
As a result, we need to introduce an intermediate datatype |El|,
\begin{myhs}
\begin{code}
data El :: [Star] -> Nat -> Star where
  El :: Lkup fam ix -> El fam ix
\end{code}
\end{myhs}
The representation of the family |fam| at index |ix| is thus given by
|RepMRec (El fam) (Lkup codes ix)|. We only need to use |El| in the first
argument, because that is the position in which we require partial application.
The second position features |Lkup| fully-applied, and can stay as is. Moreover,
in the declaration of |Family|, using |El| spares us from having to use
a proxy for |fam| in |fromMRec| and |toMRec|.

  Up to this point, we have talked about a type family and their codes as 
independent entities. As in the rest of generic programming approaches, we
want to make their relation explicit. The |Family| type class realizes this
relation, and introduces functions to perform the conversion between our
representation and the actual types:
\begin{myhs}
\begin{code}
class Family (fam :: [Star]) (codes :: [[[Atom]]]) where
  
  fromMRec  :: SNat ix  -> El fam ix                         -> RepMRec (El fam) (Lkup codes ix)
  toMRec    :: SNat ix  -> RepMRec (El fam) (Lkup codes ix)  -> El fam ix
\end{code}
\end{myhs}
One of the differences between other approaches and ours is that we do not
use an associated type to define the |codes| for a mutually recursive family
|fam|. One of the reasons to choose this path is that it alleviates the
burden of writing the longer |CodeMRec fam| every time we want to
refer to |codes|. Furthermore, there are types like lists which appear in
many different families, and in that case it makes more sense to speak about a
relation instead of a function. In any case, we can choose the other point of
the design space by moving |codes| into an associated type or introduce a
functional dependency |fam -> codes|.

Since now |fromMRec| and |toMRec| operate on families of datatypes, they have
to specify how to translate \emph{each} of the members of the family back and
forth the generic representation. This translation needs to know which is the
index of the datatype we are converting between in each case,  hence the
additional |SNat ix| parameter. For example, in the case of
or family of rose trees, |fromMRec| has the following shape:
\begin{myhs}
\begin{code}
fromMRec SZ       (El (x :>: ch))  = Rep (          Here (NA_K x :* NA_I ch :* NP0))
fromMRec (SS SZ)  (El [])          = Rep (          Here NP0 ))
fromMRec (SS SZ)  (El (x : xs))    = Rep ( There (  Here (NA_I x :* NA_I xs :* NP0)))
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
immediately obvious, but we can use Haskell's visible type
application~\cite{EisenbergWA16} to work around
it. The final |into| function, which injects a value into the corresponding |El|
is defined as follows:

\begin{myhs}
\begin{code}
into  :: forall fam ty ix dot (ix ~ Idx ty fam , Lkup fam ix ~ ty) 
      => ty -> El fam ix
into  = El
\end{code}
\end{myhs}

%format (TApp a) = "\HS{@}" a
where |Idx| is a closed type family implementing the inverse of |Lkup|, that is,
obtaining the index of the type |ty| in the list |fam|. Using this function
we can turn a |[Rose Int]| into its generic representation by writing
|fromMRec . into (TApp FamRose)|. The type application |(TApp FamRose)| is responsible
for fixing the mutually recursive family we are working with, which
let the type checker reduce all the constraints and happily inject the element
into |El|.
  
\paragraph{Deep representation.} In \Cref{sec:explicitfix} we have described a
technique to derive deep representations from shallow representations. We can
play a very similar trick here. The main difference is the definition of the
least fixpoint combinator, which receives an extra parameter of kind |Nat| indicating
which |code| to use first:
\begin{myhs}
\begin{code}
newtype Fix (codes :: [[[Atom]]]) (ix :: Nat)
  = Fix { unFix :: RepMRec (Fix codes) (Lkup codes ix) }
\end{code}
\end{myhs}
Intuitively, since now we can recurse on different positions, we need to keep
track of the representations for all those positions in the type. This is the
job of the |codes| argument. Furthermore, our |Fix| does not represent a single
datatype, but rather the \emph{whole} family. Thus, we need each value to have an
additional index to declare on which element of the family it is working on.

As in the previous section, we can obtain the deep representation by iteratively
applying the shallow representation. Last time we used |fmap| since the |RepFix|
type was a functor. |RepMRec| on the other hand cannot be given a |Functor|
instance, but we can still define a similar function |mapRec|,
\begin{myhs}
\begin{code}
mapRep :: (forall ix dot phi1 ix -> phi2 ix) -> RepMRec phi1 c -> RepMRec phi2 c
\end{code}
\end{myhs}
This type signature tells us that if we want to change the |phi1| argument in 
the representation, we need to provide a natural transformation from
|phi1| to |phi2|, that is, a function which works over each
possible index this |phi1| can take and does not change this index. 
This makes sense, as |phi1| has kind |Nat -> Star|. 
\begin{myhs}
\begin{code}
deepFrom :: Family fam codes => El fam ix -> Fix (RepFix codes ix)
deepFrom = Fix . mapRec deepFrom . from
\end{code}
\end{myhs}

\paragraph{Only well-formed representations are accepted.}
At first glance, it may seem like the |Atom| datatype gives too much freedom:
its |I| constructor receives a natural number, but there is no apparent static check
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
The lack of dependent types makes this approach very hard, in Haskell.
We would need to carry around the inhabitants |Fin n| and define functionality
to manipulate them, which is more complex than what meets the eye. 
This could greatly hinder the usability of the library.

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

Our solution is to \emph{parametrize} the |Atom| type, allowing programmers to choose
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
choosing different sets of opaque types. The |NA| datatype in this
final implementation provides two constructors, one per constructor in |Atom|.
The |NS| and |NP| datatypes do not require any change.
\begin{myhs}
\begin{code}
data NA :: (kon -> Star) -> (Nat -> Star) -> Atom -> Star where
  NA_I  :: phi    n  -> NA kappa phi (I  n)
  NA_K  :: kappa  k  -> NA kappa phi (K  k)

type RepMRec (kappa :: kon -> Star) (phi :: Nat -> Star) (c :: [[Atom]]) = NS (NP (NA kappa phi)) c
\end{code}
\end{myhs}
The |NA_K| constructor in |NA| makes use of an additional argument |kappa|.
The problem is that we are defining the code for the set of opaque types by
a specific kind, such as |Numeric| above. On the other hand, values which
appear in a field must have a type whose kind is |Star|. Thus, we require a mapping
from each of the codes to the actual opaque type they represent, this
is exactly the \emph{opaque type interpretation} |kappa|. Here is the
datatype interpreting |NumericK| into ground types:
\begin{myhs}
\begin{code}
data NumericI :: NumericK -> Star where
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
class Family (kappa :: kon -> Star) (fam :: [Star]) (codes :: [[[Atom kon]]]) where
  
  fromMRec  :: SNat ix  -> El fam ix -> RepMRec kappa (El fam) (Lkup codes ix)
  toMRec    :: SNat ix  -> RepMRec kappa (El fam) (Lkup codes ix) -> El fam ix
\end{code}
\end{myhs}

All the generic operations implemented in \texttt{\nameofourlibrary} use
parametrized version of |Atom|s and representations described in this section.
For convenience we also provide a basic set of opaque types which includes the
most common primitive Haskell datatypes.

\subsection{Combinators}

  Through the rest of this section we wish to showcase a selection of particularly
powerful combinators that are remarkably simple to define by exploiting the
\emph{sums-of-products} structure coupled with the mutual recursion information.
Defining the same combinators in \texttt{multirec} would produce much more complicated
code. In \texttt{GHC.Generics} these are even impossible to write due to the
absence of recursion information.

For the sake of fostering intuition instead of worrying about
notational overhead, we shall write values of |RepMRec kappa phi c| just like
we would write normal Haskell values. They have the same \emph{sums-of-products} 
structure anyway. Whenever a function is defined
using the |^=| symbol, |C x_1 dots x_n| will stand for a value of the corresponding
|RepMRec kappa phi c|, that is, |There (dots (Here (x_1 :* dots :* x_n :* NP0)))|. 
Since each of these |x_1 dots x_n| might be a recursive type or an opaque type,
whenever we have two functions |f_I| and |f_K| in scope, |fSq x_j| will
denote the application of the correct function for recursive positions, |f_I|,
or opaque types |f_K|. For example, here is the actual code of the function
which maps over a |NA| structure:
\begin{myhs}
\begin{code}
bimapNA f_K f_I  (NA_I  i)  = NA_I  (f_I  i)
bimapNA f_K f_I  (NA_K  k)  = NA_K  (f_K  k)
\end{code}
\end{myhs}
and this is how we write the function following this convention:
\begin{myhs}
\begin{code}
bimapNA f_K f_I x ^= fSq x
\end{code}
\end{myhs}

The first obvious combinator which we can write using the sum-of-products
structure is |map|. 
Our |RepMRec kappa phi c| is no longer a regular functor, but a higher
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
zipRep  :: RepMRec kappa1 phi1 c -> RepMRec kappa2 phi2 c -> Maybe (RepMRec (kappa1 :*: kappa2) (phi1 :*: phi2) c)
zipRep (C x_1 dots x_n) (D y_1 dots y_m)
  | C == D     ^= Just (C (x_1 :*: y_1) dots (x_n :*: y_n)) -- if C == D, then also n == m!
  | otherwise  ^= Nothing
\end{code}
\end{myhs}

  Note that it is trivial to write |zipRep| with an arbitrary
|(Alternative f)| constraint instead of |Maybe|. The |compos|
combinator, already introduced in \Cref{sec:explicitfix}, shows up in
a yet more expressive form.  We are now able to change every subtree
of whatever type we choose inside an arbitrary value of the mutually
recursive family in question.

\begin{myhs}
\begin{code}
compos  :: (forall iy dot El fam iy -> El fam iy)
        -> El fam ix -> El fam ix
compos f = toMRec . bimapRep id f . fromMRec
\end{code}
\end{myhs}

  It is worth nothing that although we presented pure versions
of these combinators, \texttt{\nameofourlibrary} defines monadic
variants of these and suffixes them with a |M|, following the
standard Haskell naming convention. We will need these monadic
combinators in \Cref{sec:alphaequivalence}.

\section{Examples}
\label{sec:mrecexamples}

In this section we present several applications of our generic programming
approach. The applications themselves -- equality, $\alpha$-equivalence, and
zippers -- are commonly introduced with any new generic library. Our goal
is to show \texttt{\nameofourlibrary} is at least as powerful as other comparable
libraries, but brings in the union of their advantages. 
Note also that even though some examples use a single recursive
datatype for the sake of conciseness, those can be readily generalized to
mutually recursive families.

There are many other applications for generic programming which greatly benefit
from supporting mutual recursion, if not requiring it. 
One great pool of examples is operations with abstract syntax trees of realistic
languages, such as generic diff-ing~\cite{CacciariMiraldo2017} or
pretty-printing~\cite{Magalhaes2010}.

\subsection{Equality}

  Following the unspoken law of generic programming papers,
one is obliged to define generic equality in one's generic programming
framework. Using \texttt{\nameofourlibrary} one can define a particularly
elegant version of generic equality:

\begin{myhs}
\begin{code}
geq  ::  (Family kappa fam codes) 
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

% Usual problems such as $\alpha$-equality, although already treated using generic
% programming~\cite{Weirich2011}, still creeps back up when more than one 
% datatype enters the stage.

  Syntactic equality is definitely a must, but it is a ``no sweat''
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
$\lambda$-calculus and their generic pattern synonyms:

%format LambdaTerm = "\HT{Term_{\lambda}}"
\begin{minipage}[t]{.32\textwidth}
\begin{myhs}
\begin{code}
data LambdaTerm  
  =  Var  String
  |  Abs  String      LambdaTerm
  |  App  LambdaTerm  LambdaTerm
\end{code}
\end{myhs}
\end{minipage}
\begin{minipage}[t]{.45\textwidth}
\vspace{1em}
\begin{myhs}
\begin{code}
pattern (Pat Var) x    = Tag           CZ    (NA_K x :* NP0)
pattern (Pat Abs) x t  = Tag      (CS  CZ))  (NA_K x :* NA_I t :* NP0)
pattern (Pat App) t u  = Tag (CS  (CS  CZ))  (NA_I t :* NA_I u :* NP0) 
\end{code}
\end{myhs}
\end{minipage}

  The process is conceptually simple. Firstly, for |t_1, t_2 :: LambdaTerm|
to be $\alpha$-equivalent, they have to have the same structure, that
is, the same constructors. Otherwise, we can already say they are not
$\alpha$-equivalent.  We then traverse both terms at the same time and
every time we go through a binder, in this case |Abs|, we register a
new \emph{rule} saying that the bound variable names are equivalent
for the terms under that scope. Whenever we find a reference to a
variable, |Var|, we check if the referenced variable is either exactly
the same or equivalent under the registered \emph{rules} so far.

  Let us abstract away this book-keeping functionality by the means of
a monad with a couple associated functions. The idea is that |m| will
keep track of a stack of scopes, each scope will be registering a list
of \emph{name-equivalences}. In fact, this is very close to how one
should go about defining equality for \emph{nominal terms}~\cite{Calves2008}.

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
    galphaEq x y = maybe False (go (Pat Term)) (zipRep x y)

    step = elimRepM  (return . uncurry (==))  -- Opaque types have to be equal!
                     (uncurry galphaEq)       -- recursive step
                     (return . and)           -- combining results

    go (Pat LambdaTerm) x = case sop x of
      (Pat Var) (v_1 :*: v_2)                -> v_1 =~= v_2
      (Pat Abs) (v_1 :*: v_2) (t_1 :*: t_2)  -> scoped (addRule v_1 v_2 >> galphaEq t_1 t_2)
      _                                      -> step x
\end{code}
\end{myhs}

  There is a number of things going on with this example. First,
note the application of |zipRep|. If two |LambdaTerm|s are made with different
constructors, |galphaEq| will already return |False| because |zipRep| will fail.
When |zipRep| succeeds though, we get access to one constructor with
paired fields inside. Then the |go| function enters the stage, it 
is performing the necessary semantic actions for the |Var| and |Abs|
constructors and applying a general eliminator for anything else.
In the actual library, the \emph{pattern synonyms} are automatically 
generated as we will see on \Cref{sec:templatehaskell}.

  One might be inclined to believe that the generic programming here
is more cumbersome than a straight forward pattern matching definition
over |LambdaTerm|.  If we bring in a more intricate language to the
spotlight, however, manual pattern matching becomes almost intractable
very fast.

Take the a toy imperative language defined in \Cref{fig:alphatoy}.
Transporting |alphaEq| from the lambda calculus is fairly simple. For
one, |alhaEq|, |step| and |galphaEq| remain the same.  We just need to
adapt the |go| function. On the other hand, having to write
$\alpha$-equivalence by pattern matching might not be so straight
forward anymore. Moreover, if we decide to change the toy language and
add more statements or more expressions, the changes to the |go|
function are minimal, if any. As long as we do not touch the
constructors that |go| patterns matches on, we can use the very same
function.

\begin{figure}
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
go (Pat Stmt)  x = case sop x of
      (Pat SAssign) (v_1 :*: v_2) (e_1 :*: e_2)  
         ->  addRule v_1 v_2 >> galphaEq e_1 e_2
      _  ->  step x
go (Pat Decl)  x = case sop x of
      (Pat DVar) (v_1 :*: v_2) 
         ->  addRule v_1 v_2 >> return True
      (Pat DFun) (f_1 :*: f_2) (x_1 :*: x_2) (s_1 :*: s_2)
         ->  addRule f_1 f_2   
         >>  scoped (addRule x_1 x_2 >> galphaEq s_1 s_2)
      _  ->  step x
go (Pat Exp)   x = case sop x of
      (Pat EVar) (v_1 :*: v_2)
         ->  v_1 =~= v_2
      (Pat ECall) (f_1 :*: f_2) (e_1 :*: e_2)
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
Zippers~\cite{Huet1997} are a well established technique for 
traversing a recursive data structure keeping track of the current
\emph{focus point}. Defining generic zippers is nothing new,
this has been done by many authors~\cite{Hinze2004,Adams2010,Yakushev2009}
for many different classes of types in the past. To the best of
the authors knowledge, this is the first definition in a direct
\emph{sums-of-products} style. Moreover, being able to define
the generic zipper in one's generic programming framework is
a non-trivial expressivity benchmark to be achieved. We will not
be explaining what \emph{are} zippers in detail, the unfamiliar 
reader should check the references. Instead, we will give a quick
reminder and show how zippers fit within our framework instead.

  Generally speaking, the zipper keeps track of a focus point in a
data structure and allows for the user to conveniently move this focus
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

  Where |a| and |Loc a| are isomorphic, and can be converted by the
means of |enter| and |leave| functions. For instance, the composition
of |down|, |down|, |right| , |update f| will essentially move the
focus two layers down from the root, then one element to the right and
apply function |f| to the focused element, as shown in \Cref{fig:zipperpic}.

\begin{figure}
\begin{center}
\begin{tabular}{m{.2\linewidth} m{.06\linewidth} m{.2\linewidth}}
\begin{forest}
  [|a|,draw [|b| [|c_1|] [|c_2|] [|c_3|]] [|d|]]
\end{forest}
  & { \centering $\Rightarrow$ } &
\begin{forest}
  [|a| [|b| [|c_1|] [|f c_2|,draw] [|c_3|]] [|d|]]
\end{forest}
\end{tabular}
\end{center}
\caption{Graphical representation of |down| , |down| , |right| and |update f|}
\label{fig:zipperpic}
\end{figure}

  In our case, this location type consists in a distinguished element
of type |ix| and a stack of contexts with a hole of type |ix|, where
we can plug the distinguished element and \emph{leave} the zipper.
This stack of contexts are used to keep track of how far deep from the
root we are.  All of the following development is parametrized by an
interpretation for opaque types |ki :: kon -> Star|, a family |fam ::
[Star]| and its associated codes |codes :: [[[Atom kon]]]|; since these
are the same for any given family, let us fix those and omit them
from the declarations to simplify the presentation.

  A location for the |ix| element of the family, |El fam ix|
is defined by having a distinguished element of the family, possibly of
a different index, |iy| and a stack of contexts that represent a value of
type |El fam ix| with a \emph{hole} of type |El fam iy|.

\begin{myhs}
\begin{code}
data Loc :: Nat -> Star where
  Loc :: El fam iy -> Ctxs ix iy -> Loc ix
\end{code}
\end{myhs}

  The stack of contexts represent how deep into the recursive
tree we have descended so far. Each time we unwrap another layer of recursion,
we push some context into the stack to be able to ascend back up. Note how
the |Cons| constructor resembles some sort of composition operation.

\begin{myhs}
\begin{code}
data Ctxs :: Nat -> Nat -> Star where
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
data Ctx :: [[Atom kon]] -> Nat -> Star where
  Ctx :: Constr n c -> NPHole (Lkup n c) iy -> Ctx c iy

data NPHole :: [Atom kon] -> Nat -> Star where
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
data NPHoleE :: [Atom kon] -> Star where
  Witness :: El fam ix -> NPHole c ix -> NPHoleE c
\end{code}
\end{myhs}

  Finally, we can define the |firstE| and |nextE| that are used
instead of the |first| and |next| from \texttt{multirec}. The intuition
behind those is pretty simple: |firstE| returns the |NPHole| with the 
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
Here |enter| and |leave| witness the isomorphism between |El fam ix|
and |Loc ix|.

\begin{minipage}[t]{.55\textwidth}
\begin{myhs}
\begin{code}
tr :: LambdaTerm -> Maybe LambdaTerm
tr = enter  >>>  down 
            >=>  right 
            >=>  update (const $ Var "c") 
            >>>  leave 
            >>>  return
\end{code} %$
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

  We invite the reader to check the source code for a more detailed
account of the generic zipper, which is the last example we introduce.
The selection of examples show that by keeping the good ideas from
the generic programming community and putting them all under the same roof
we are able to achieve powerful functionality in a convenient fashion.

  The last point we have to address is that we still have to write
the |Family| instance for the types we want to use. For instance,
the |Family| instance for example in \Cref{fig:alphatoy} is not going
to be fun. Deriving these automatically is possible, but non-trivial,
as we shall see in \Cref{sec:templatehaskell} 

\section{Template Haskell}
\label{sec:templatehaskell}

  Having a convenient and robust way to get the |Family| instance for
a certain selection of datatypes is paramount for the usability of the
library. The goal is to take mechanical work away from the
programmer. In a real scenario, the typical mutually recursive family
will be constituted of dozens of datatypes with tens of dozens of
constructors. Sometimes these datatypes are written with parameters,
or come from external libraries. We wish to handle all of those,
but first, there are some challenges we need to overcome.

  The design goal here is that the programmer can derive her |Family|
instance with minimum effort by calling some \emph{Template Haskell}~\cite{Sheard2002}
functionality, ie:

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

  The |deriveFamily| receives only the topmost (ie, the first) type of
the family and should unfold the (type level) recursion until it
reaches a fixpoint.  In this case, the |type FamProgString = P [Prog
String , dots]| will be generated, together with its |Family|
instance. Optionally, one can also give a custom function to decide
whether something is an Opaque type or not. By default, it uses a
selection of Haskell built-in types as opaque types.

\subsection{Unfolding the Family}
\label{sec:underthehood}

  The process of deriving a whole mutually recursive family from a single
member is mainly divided in two disjoint process. First we unfold all definitions
and follow all the recursive paths until we reach a fixpoint and, hence,
have discovered all types in the family. Second, we translate the definition
of the previously discovered types to the format our library expects.
During the unfolding process we keep a key-value map in a 
|State| monad, keeping track of the types we have seen, the types we have
seen \emph{and} processed and the indexes of those within the family.

  Let us illustrate this process in a bit more detail using the canonical
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

  The first thing that happens is registering that we seen the type |Rose Int|.
This associates it with a fresh index, in this case, |Z|. We have not yet processed it, however!
To do that, we need to reify the definition of |Rose|. At this point, \emph{Template Haskell}
will return |data Rose x = x :>: [Rose x]|. This has kind |Star -> Star| and cant
be directly translated. In our case, we just need the specific case where |x = Int|.
Essentially, we just apply the reified definition of |Rose| to |Int| and $\beta$-reduce it,
giving us |Int :>: [Rose Int]|. The next processing step is looking into
the types of the fields of the (single) constructor |:>:|: First we see |Int| and
decide it is an opaque type, say |KInt|. Secondly, we see |[Rose Int]| and
notice it is the first time we see this type. Hence, we register it with a fresh
index, which now has to be |S Z| and return |P [P [K KInt, I (S Z)]]| as the
processed type of |Rose Int|. We now go into |[Rose Int]| for processing. The
idea is the same: reify, then substitute, then process each field of
each constructor.

\begin{enumerate}
  \item |reify [] =~= data [x] = nil || x : [x]|
  \item Substituting |x| for |Rose Int| gives |nil || (Rose Int) : [ Rose Int ]|.
  \item |nil| has no fields. We have already seen |Rose Int|, it is indexed by |Z|.
        We have also seen |[Rose Int]|, it is indexed by |S Z|.
  \item return |P [ P [] , P [I Z , I (S Z)] ]| as the processed type of |[Rose Int]|.
\end{enumerate}

  Since we have not seen any new type in (4) above, there is nothing else
to process. Essentially, the hard part has been done. Now we just have to 
generate the Haskell code. This is a very verbose and mechanical process, whose
details will be omitted. Nevertheless, we generate type synonyms,
pattern synonyms, the |Family| instance and metadata information. 
The generated type synonyms are named after the topmost type of the family,
passed to |deriveFamily|:

\begin{myhs}
\begin{code}
type FamRoseInt    = P [ Rose Int                    , [Rose Int] ]
type CodesRoseInt  = P [ (P [P [K KInt , I (S Z)]])  , P [ P [] , P [I Z , I (S Z) ] ] ]
\end{code}
\end{myhs}

  Pattern synonyms are useful for convenient pattern matching and injecting over
the |View| datatype. Some |SNat| representing the index of each
type in the family also come in handy. These have the same name as the original 
but with an added \emph{underscore}:

\begin{myhs}
%format forkP = "\HT{\overline{\triangleright}}" 
%format nilP  = "\HT{\overbar{[]}}" 
%format consP = "\HT{\overline{:}}" 
\begin{code}
pattern x forkP xs  = Tag SZ       (NA_K x :* NA_I xs :* NP0)
pattern nilP        = Tag SZ       NP0
pattern x consP xs  = Tag (SS SZ)  (NA_I x :* NA_I xs :* NP0)

pattern (Pat RoseInt)      = SZ
pattern (Pat ListRoseInt)  = SS SZ
\end{code}
\end{myhs}

  The actual |Family| instance is exactly as the one shown in \Cref{sec:family}

\begin{myhs}
\begin{code}
instance Family Singl FamRoseInt CodesRoseInt where
  dots
\end{code}
\end{myhs}

  Finally, we also generate some metadata for being able to correlate
the name of constructors and types with the generic representation. 
We handle metadata almost entirely like \texttt{generics-sop}, with a 
few differences that will be explained in \Cref{sec:metadata}

\subsection{Metadata}
\label{sec:metadata}

  The representations described up to now are enough to write generic equalities
and zippers. But there is one missing ingredient to derive generic
pretty-printing or conversion to JSON, for instance. We need to maintain
the \emph{metadata} information of our datatypes.
This metadata includes the datatype name, the module where it was defined,
and the name of the constructors, among other information. Without this
information you cannot write a function which outputs the string
\begin{verbatim}
1 :>: [2 :>: [], 3 :>: []]
\end{verbatim}
for a call to |genericShow (1 :>: [2 :>: [], 3 :>: []])|. The reason is that
the code of |Rose Int| does not contain the information that the constructor
of |Rose| is called |:>:|.


  Like in \texttt{generics-sop}~\cite{deVries2014}, having the code
for a family of datatypes at hand allows for a completely separate
treatment of metadata. This is yet another advantage from the
sum-of-products approach when compared to the more traditional pattern
functors. In fact, our handling of metadata is heavily inspired from
\texttt{generics-sop}, so much so that we start explaining a simplified version of how
they handle metadata, then outline the differences to our approach. 

\begin{myhs}
\begin{code}
data DatatypeInfo :: [[Star]] -> Star where
  ADT  :: ModuleName -> DatatypeName -> NP  ConstructorInfo cs       -> DatatypeInfo cs
  New  :: ModuleName -> DatatypeName ->     ConstructorInfo (P [c])  -> DatatypeInfo (P [ P [ c ]])

data ConstructorInfo :: [Star] -> Star where
  Constructor  :: ConstructorName                             -> ConstructorInfo xs
  Infix        :: ConstructorName -> Associativity -> Fixity  -> ConstructorInfo (P [ x, y ])
  Record       :: ConstructorName -> NP FieldInfo xs          -> ConstructorInfo xs

data FieldInfo :: Star -> Star where
  FieldInfo :: FieldName -> FieldInfo a
\end{code}
\end{myhs}
This information is tied to a datatype by means of an additional type class:
\begin{myhs}
\begin{code}
class HasDatatypeInfo a where
  datatypeInfo :: proxy a -> DatatypeInfo (Code a)
\end{code}
\end{myhs}
Generic functions may now query the metadata by means of functions like
|datatypeName|, which reflect the type information into the term level.

Our library uses the same approach to handle metadata. In fact, the code remains
almost unchanged, except for adapting it to the larger universe of
datatypes we can now handle. Unlike \texttt{generic-sop}, our list of lists
representing the sum-of-products structure does not contain types of kind |Star|,
but |Atom|s. All the types representing metadata at the type level must be
updated to reflect this new scenario:
\begin{myhs}
\begin{code}
data DatatypeInfo     :: [  [  Atom kon ]]  -> Star where
data ConstructorInfo  ::    [  Atom kon ]   -> Star where
data FieldInfo        ::       Atom kon     -> Star where
\end{code}
\end{myhs}

As we have discussed above, our library is able to generate codes not only
for single types of kind |Star|, like |Int| or |Bool|, but also for types which
result of type level applications, such as |Rose Int| or |[Rose Int]|.
The shape of the metadata information in |DatatypeInfo|, a module name plus
a datatype name, is not enough to handle these cases. We introduce a new
|TypeName| which may contain applications, and upgrade |DatatypeInfo| to
use it instead.
\begin{myhs}
\begin{code}
data TypeName  =  ConT ModuleName DatatypeName
               |  TypeName :@: TypeName

data DatatypeInfo :: [[Atom kon]] -> Star where
  ADT  :: TypeName  -> NP  ConstructorInfo cs       -> DatatypeInfo cs
  New  :: TypeName  ->     ConstructorInfo (P [c])  -> DatatypeInfo (P [ P [ c ]])
\end{code}
\end{myhs}

The most important difference to \texttt{generics-sop}, perhaps, 
is that the metadata is not defined for a single type, but
for a type \emph{within} a family. This is reflected in the new signature of 
|datatypeInfo|, which receives proxies for both the family and the type.
The type equalities in that signature reflect the fact that the given type
|ty| is included with index |ix| within the family |fam|. This step is needed
to look up the code for the type in the right position of |codes|.
\begin{myhs}
\begin{code}
class (Family kappa fam codes) => HasDatatypeInfo kappa fam codes ix | fam -> kappa codes where
  datatypeInfo  :: (ix ~ Idx ty fam , Lkup ix fam ~ ty)
                => Proxy fam -> Proxy ty -> DatatypeInfo (Lkup ix codes)
\end{code}
\end{myhs}

  The Template Haskell will then generate something similar to
the instance below for the first type in the family, |Rose Int|:

\begin{myhs}
\begin{code}
instance HasDatatypeInfo Singl FamRose CodesRose Z where
  datatypeInfo _ _  =  ADT (ConT "Example" "Rose" :@: ConT "Prelude" "Int")
                    $  (Constructor ":>:") :* NP0
\end{code} %$
\end{myhs}
  

\section{Conclusion and Future Work}

  In this paper we have presented \texttt{\nameofourlibrary}, a
library for generic programming in Haskell that combines the
advantages of previous approaches to generic programming. We have
carefully blended the information about (mutually) recursive
positions, from \texttt{multirec}, with the sums-of-products codes,
from \texttt{generics-sop}, maintaining the advantages of both. The
result is as expressive as other approaches such as \texttt{multirec},
yet it allows for a more concise combinator-based approach to defining
generic functions. Our library will be made publicly available on
Hackage once the review process is done. 

  Future work involves expanding the universe of datatypes that our library
can handle. Currently, every type involved in a recursive family must be
a ground type (of kind |Star| in Haskell terms); our Template Haskell derivations
acknowledges this fact by implementing some amount of reduction for types.
This limits the functions we can implement generically, for example we cannot
write a generic |fmap| function, since it operates on types of kind |Star -> Star|.
\texttt{GHC.Generics} supports type constructors with exactly one argument
via the \texttt{Generic1} type class. We foresee most of the complexity to
be in the definition of |Atom|, as it must support some kind of application
of type constructors to other parameters or opaque types.

The original sum-of-products approach does not handle all the ground types either,
only regular ones~\cite{deVries2014}. We inherit this restriction, and cannot
represent recursive families which involve existentials or GADTs. The problem
in this case is representing the constraints that each constructor imposes
on the type arguments.