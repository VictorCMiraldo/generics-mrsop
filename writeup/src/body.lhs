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
and |Rep (Bin a)|.  All this information is tied to the original
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
\Cref{sec:designspace}. Some libraries, mainly deriving from the \texttt{SYB}
approach~\cite{Lammel2003,Mitchell2007}, use the |Data| and |Typeable| type classes
instead of static type level information to provide generic functionality. 
These are a completely different strand of work from ours.

  \Cref{fig:gplibraries} shows the main libraries relying on type
level representations. In the \emph{pattern functor} approach we have
\texttt{GHC.Generics}~\cite{Magalhaes2010}, being the most commonly
used one, that effectively replaced \texttt{regular}~\cite{Noort2008}.
The former does not account for recursion explicitly, allowing only for a \emph{shallow} representation.
Whereas the later allows for both \emph{deep} and \emph{shallow} representations
by maintaining information about the recursive occurrences of a
type. Maintaining this information is central to some generic
functions, such as the generic |map| and |Zipper|, for instance. 
Oftentimes though, one actually needs more than just one recursive
type, justifying the need to \texttt{multirec}~\cite{Yakushev2009}.

These libraries are too permissive though, for instance, |U1 :*: Maybe|
is a perfectly valid \texttt{GHC.Generics} \emph{pattern functor} but
will break generic functions.  The way to fix this is to ensure that the
\emph{pattern functors} abide by a certain format, by defining them
by induction on some \emph{code}, that can be
inspected and matched on. This is the approach of
\texttt{generics-sop}~\cite{deVries2014}. The more restrictive
code approach allows one to write concise, combinator-based,
generic programs. The novelty in our work is in the intersection of
both the expressivity of \texttt{multirec}, allowing the encoding of
mutually recursive families, with the convenience of the more modern
\texttt{generics-sop} style.

\begin{figure}\centering
\ra{1.3}
\begin{tabular}{@@{}lll@@{}}\toprule
                        & Pattern Functors       & Codes                 \\ \midrule
  No Explicit Recursion & \texttt{GHC.Generics}  & \texttt{generics-sop} \\
  Simple Recursion      &  \texttt{regular}      &  \multirow{2}{*}{\textbf{\texttt{\nameofourlibrary}}} \\
  Mutual Recursion      &  \texttt{multirec}     &   \\
\bottomrule
\end{tabular}
\caption{Spectrum of static generic programming libraries}
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
illustrating how it subsumes the features of the previous approaches.
\item We provide Template Haskell functionality to derive all the
boilerplate code needed to use our library (\Cref{sec:templatehaskell}).
The novelty lies in our handling of instantiated type constructors.
\end{itemize}
We have packaged our results as a Haskell library, \texttt{\nameofourlibrary},
which is being delivered as supplementary material. 
This library fills the hole in \Cref{fig:gplibraries} for a code-based
approach with support for mutual recursion.

\subsection{Design Space}
\label{sec:designspace}

The availability of several libraries for generic programming witnesses
the fact that there are trade-offs between expressivity,
ease of use, and underlying techniques in the design of such a library.
In this section we describe some of these trade-offs, especially those
to consider when using the static approach.

\paragraph{Explicit Recursion.}
There are two ways to define the representation of values. Those
that have information about which fields of the constructors of 
the datatype in question are recursive versus those that do not. 

If we do not mark recursion explicitly, \emph{shallow} encodings are
our sole option, where only one layer of the value is turned into a
generic form by a call to |from|.  This is the kind of representation
we get from \texttt{GHC.Generics}, among others.  The other side of
the spectrum would be the \emph{deep} representation, in which the
entire value is turned into the representation that the generic
library provides in one go.

Marking the recursion explicitly, like in \texttt{regular}~\cite{Noort2008},
allows one to choose between \emph{shallow} and \emph{deep} encodings
at will. These representations are usually more involved as they
need an extra mechanism to represent recursion. 
In the |Bin| example, the description of the |Bin|
constructor changes from ``this constructors has two fields of the
|Bin a| type'' to ``this constructor has two fields in which you
recurse''. Therefore, a \emph{deep} encoding requires some explicit
\emph{least fixpoint} combinator -- usually called |Fix| in Haskell.

Depending on the use case, a shallow representation might be more efficient if only
part of the value needs to be inspected. On the other hand, deep
representations are sometimes easier to use, since the conversion is
performed in one go, and afterwards one only have to work with
the constructs from the generic library.

The fact that we mark explicitly when recursion takes place in a
datatype gives some additional insight into the description.
Some functions really need the information
about which fields of a constructor are recursive and which are not,
like the generic |map| and the generic |Zipper| -- we describe
the latter in \Cref{sec:mrecexamples}.
This additional power also has been used to define regular
expressions over Haskell datatypes~\cite{Serrano2016}. 

\paragraph{Sum of Products}

Most generic programming libraries build their type level descriptions out of three basic
combinators: (1) \emph{constants}, which indicate a type is atomic and should not
be expanded further; (2) \emph{products} (usually written as |:*:|) which are used to
build tuples; and (3) \emph{sums} (usually written as |:+:|) which
encode the choice between constructors. |Rep (Bin a)| above is expressed in
this form. Note, however, that there is no restriction on \emph{how} these
can be combined. 

In practice, one can always use a sum of products to represent a datatype -- a sum
to express the choice of constructor, and within each constructor a product to
declare which fields you have. The \texttt{generic-sop} library~\cite{deVries2014}
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
datatype, which is the one being defined. Sometimes one would like to have the
mutually recursive structure handy, though. 
The syntax of many programming languages, for instance, is expressed naturally using
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
data Rose  a  =  Fork a [Rose a]
data []    a  =  [] | a : [a]
\end{code}
\end{myhs}
The mutual recursion becomes apparent once one instantiaties |a| to some
ground type, for instance:
\begin{myhs}
\begin{code}
data RoseI  =  Fork Int ListI
data ListI  =  Nil | RoseI : ListI
\end{code}
\end{myhs}

The \texttt{multirec} library~\cite{Yakushev2009} is a generalization of
\texttt{regular} which handles mutually recursive families using this very technique. 
The mutual recursion is central to some applications such as generic 
diffing~\cite{CacciariMiraldo2017} of abstract syntax trees.

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

  Since version $7.2$, GHC supports some off the shelf generic
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
|fromGen| is, in fact, the |from| in module |GHC.Generics|.

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
representations. Here, they are \emph{pattern functors}. 

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
constant functor |K1|. We require an instance of |Size|
so we can successfully tie the recursive knot.

\begin{myhs}
\begin{code}
instance (Size x) => GSize (K1 R x) where
  gsize (K1 x) = size x
\end{code}
\end{myhs}

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

  To finish the description of the generic |size| for any datatype,
we also need instances for the
\emph{unit}, \emph{void} and \emph{metadata} pattern functors,
called |U1|, |V1|, and |M1| respectively. Their |GSize| is
rather uninteresting, so we omit them for the sake of conciseness.

  This technique of \emph{mutually recursive classes} is quite 
specific to \texttt{GHC.Generics} flavor of generic programming.
\Cref{fig:sizederiv} illustrates how the compiler go about choosing
instances for computing |size (Bin (Leaf 1) (Leaf 2))|. 
In the end, we just need an instance for |Size Int| to compute
the final result. Literals of type |Int| illustrate
what we call \emph{opaque types}: those types that constitute the base
of the universe and are \emph{opaque} to the representation language.

  In practice, one usually applies yet another maneuver to make this
process more convenient. Note that the implementation of |size| for
|Bin a| relies on the implementation of |gsize|, after converting a |Bin a|
to its generic representation. We can instruct GHC to do this automatically
using \emph{default method signatures}~\cite[section 9.8.1.4]{ghcUsersGuide} and modifying the |Size| class to:

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
marked as $(\dagger)$ in \Cref{fig:sizederiv}: after unwrapping the calculation
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
explicit \emph{sums-of-products} structure to forget this
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

  There are still downsides to this approach. A notable
one is the need to carry constraints around: the actual |gsize|
written with the \texttt{generics-sop} library and no sugar
reads as follows.

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

\section{Explicit Fix: Deriving Deep and Shallow Representations}
\label{sec:explicitfix}

  In this section we will start to look at our approach, essentially
combining the techniques from the \texttt{regular} and \texttt{generics-sop}
libraries. Later we extend the constructions to handle mutually recursive
families instead of simple recursion. As we discussed in the introduction,
a fixpoint view over generic functionality is required
to implement some functionality like the |Zipper| generically.
In other words, we need a explicit description of which fields of
a constructor are recursive and which are not.

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
to its representation is straightforward:

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

  In order to define |RepFix| we just need to a way to map an |Atom| into |Star|.
Since an atom can be either an opaque type, known statically, or some other
type that will be used as a recursive position later on, we simply receive
it as another parameter. The |NA| datatype relates an |Atom| to its semantics:

\begin{myhs}
\begin{code}
data NA :: Star -> Atom -> Star where
  NA_I  :: x    -> NA x I
  NA_K  :: Int  -> NA x KInt

newtype RepFix a x = Rep { unRep :: NS (NP (NA x)) (CodeFix a) }
\end{code}
\end{myhs}

  It is a interesting exercise to implement the |Functor (RepFix a)| instance.
We were only able to lift it to a functor by recording the information about
the recursive positions. Otherwise, there would be no way to know where to apply |f|
when defining |fmap f|.

  Nevertheless, working directly with |RepFix| is hard -- we need to
pattern match on |There| and |Here|, whereas we actually want to have
the notion of \emph{constructor} for the generic setting too!  The
main advantage of the \emph{sum-of-products} structure is to allow a
user to pattern match on generic representations just like they would
on values of the original type, contrasting with
\texttt{GHC.Generics}. One can precisely state that a value of a
representation is composed of a choice of constructor and its
respective product of fields by the |View| type.  A value of |Constr n
sum| is a proof that |n| is a valid constructor for |sum|, essentially
saying |n < length sum|. The |Lkup| is just a type level list lookup,
we will come back it in more details in \Cref{sec:family}.

\begin{myhs}
\begin{code}
data View :: [[ Atom ]] -> Star -> Star where
  Tag :: Constr n sop -> NP (NA x) (Lkup sop n) -> View sop x
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
reach a given index |n| that is out of bounds. Interestingly, our design
guarantees that this case is never reached by the definition of |Constr|.

  Now we are able to easily pattern match and inject into and from
generic values.  Unfortunately, matching on |Tag| requires describing
in full detail the shape of the generic value using the elements of
|Constr|. Using pattern synonyms~\cite{Pickering2016} we can define
those patterns once and for all, and give them more descriptive names.
For example, here are the synonyms describing the constructors |Bin|
and |Leaf| as |View (Code (Bin Int)) x|: \footnote{Throughout this
paper we use the syntax |(Pat C)| to refer to the pattern describing a
view for constructor |C|.}

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
inj  :: View    sop  x  -> RepFix  sop  x
sop  :: RepFix  sop  x  -> View    sop  x
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
tree and adding one to its leaves. This example is a bit convoluted,
since one could get the same result by simply writing 
|fmap (+1) :: Bin Int -> Bin Int|, but shows the intended usage
of the |compos| combinator just defined.

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
  
\paragraph{Converting to a deep representation.}  The |fromFix| function
returns a shallow representation. But by constructing the least
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

  So far, we handle the same class of types
as the \texttt{regular}~\cite{Noort2008} library, but we are imposing 
the representation to follow a \emph{sum-of-products} structure
by the means of |CodeFix|. Those types are guaranteed to have an
initial algebra, and indeed, the generic fold is defined
as expected: 

\begin{myhs}
\begin{code}
fold :: (RepFix a b -> b) -> Fix (RepFix a) -> b
fold f = f . fmap (fold f) . unFix
\end{code}
\end{myhs}

\begin{figure}
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
\caption{Generic |crush| combinator}
\label{fig:crush}
\end{figure}

  Sometimes we actually want to consume a value and produce
a single value, but does not need the full expressivity of |fold|. 
Instead, if we know how to consume the opaque types and combine
those results, we can consume any |GenericFix| type using |crush|,
which is defined in \cref{fig:crush}.

  Finally, we come full circle to our running |gsize| example
as it was promised in the introduction. This is noticeably the smallest
implementation so far, and very straight to the point.

\begin{myhs}
\begin{code}
gsize :: (Generic a) => a -> Int
gsize = crush (const 1) sum
\end{code}
\end{myhs}

  Let us take a step back and reflect upon what we have achieved
so far. We have combined the insight from
the \texttt{regular} library of keeping track of recursive positions
with the convenience of the \texttt{generics-sop} for enforcing a
specific \emph{normal form} on representations. By doing so, we were
able to provide a \emph{deep} encoding for free. This essentially frees
us from the burden of maintaining complicated constraints needed for
handling the types within the topmost constructor. The information
about the recursive position allows us to write neat combinators like
|crush| and |compos| together with a convenient |View| type for
easy generic pattern matching. The only thing keeping us from
handling real life applications is the limited form of recursion. When
a user requires a generic programming library, chances are they need
to traverse and consume mutually recursive structures.

\section{Mutual Recursion}
\label{sec:family}

  Conceptually, going from regular types (\Cref{sec:explicitfix}) to
mutually recursive families is simple. We just need to be able to reference
not only one type variable, but one for each element in the family.
This is usually~\cite{Loh2011,Altenkirch2015} done by adding an index to the
recursive positions that represents which member of the family we are recursing over.
As a running example, we use the \emph{rose tree} family from the
introduction.
\begin{myhs}
\begin{code}
data Rose  a  =  Fork a [Rose a]
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
the member of the family to recurse into:
\begin{myhs}
\begin{code}
data Atom  = I Nat | KInt | dots

data Nat   = Z | S Nat
\end{code}
\end{myhs}
The code of this recursive family of datatypes can finally be described as:
\begin{myhs}
\begin{code}
type FamRose           = P [Rose Int, [Rose Int]]

type CodeMRec FamRose  = (P  [ (P [ (P [ KInt, I (S Z)])])          -- code for Rose Int
                             , (P [ (P []), P [ I Z, I (S Z)]])])   -- code for [Rose Int]
\end{code}
\end{myhs}
Let us have a closer look at the code for |Rose Int|, which appears in the
first place in the list. There is only one constructor which has an |Int| field,
represented by |KInt|, and another in which we recurse via the second member of 
our family (since lists are 0-indexed, we represent this by |S Z|). Similarly,
the second constructor of |[Rose Int]| points back to both |Rose Int|
using |I Z| and to |[Rose Int]| itself via |I (S Z)|.

  Having settled on the definition of |Atom|, we now need to adapt |NA| to
the new |Atom|s. In order to interpret any |Atom| into |Star|, we now need
a way to interpret the different recursive positions. This information is given
by an additional type parameter |phi| that maps natural numbers into types.
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
The only piece missing here is tying the recursive loop. If we want our
representation to describe a family of datatypes, the obvious choice
for |phi n| is to look the type at index |n| in |FamRose|. In fact,
we are simply performing a type level lookup in the family in question.
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
of types. Let |fam| be a family of types, like
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
that \texttt{GHC.Generics} would have chosen for |Rose Int|:
\begin{myhs}
\begin{code}
 RepMRec  (Lkup FamRose) (Lkup (CodeMRec FamRose) Z)
  =    RepMRec  (Lkup FamRose)      (P [ (P [ KInt, I (S Z)])])
  =    NS (NP (NA (Lkup FamRose)))  (P [ (P [ KInt, I (S Z)])])
  ==   K1 R Int :*: K1 R (Lkup FamRose (S Z))
  =    K1 R Int :*: K1 R [Rose Int]
  =    RepGen (Rose Int)
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
The second position has |Lkup| already fully-applied, and can stay as is. Moreover,
in the declaration of |Family|, using |El| spares us from using
a proxy for |fam| in |fromMRec| and |toMRec|.

  We still have to relate a family of types to their respective codes.
As in other generic programming approaches, we want to make their
relation explicit. The |Family| type class below realizes this
relation, and introduces functions to perform the conversion between
our representation and the actual types:

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
many different families, and in that case it makes sense to speak about a
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
fromMRec SZ       (El (Fork x ch))  = Rep (          Here (NA_K x :* NA_I ch :* NP0))
fromMRec (SS SZ)  (El [])           = Rep (          Here NP0 ))
fromMRec (SS SZ)  (El (x : xs))     = Rep ( There (  Here (NA_I x :* NA_I xs :* NP0)))
\end{code}
\end{myhs}
By pattern matching on the index, the compiler knows which family member
to expect as a second argument. In dependently-typed languages such as Agda or
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
intermediate datatype. Our |fromMRec| function does not take a member of
the family directly, but an |El|-wrapped one. However, to construct that value,
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
allows the type checker to reduce all the constraints and happily inject the element
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
applying the shallow representation. Earlier we used |fmap| since the |RepFix|
type was a functor. |RepMRec| on the other hand cannot be given a |Functor|
instance, but we can still define a similar function |mapRec|,
\begin{myhs}
\begin{code}
mapRep :: (forall ix dot phi1 ix -> phi2 ix) -> RepMRec phi1 c -> RepMRec phi2 c
\end{code}
\end{myhs}
This signature tells us that if we want to change the |phi1| argument in 
the representation, we need to provide a natural transformation from
|phi1| to |phi2|, that is, a function which works over each
possible index this |phi1| can take and does not change this index. 
This follows from |phi1| having kind |Nat -> Star|. 
\begin{myhs}
\begin{code}
deepFrom :: Family fam codes => El fam ix -> Fix (RepFix codes ix)
deepFrom = Fix . mapRec deepFrom . from
\end{code}
\end{myhs}

\paragraph{Only well-formed representations are accepted.}
At first glance, it may seem like the |Atom| datatype gives too much freedom:
its |I| constructor receives a natural number, but there is no apparent static check
that this number refers to an actual member of the recursive family we
are describing. For example, the list of codes
|(P [ (P [ (P [ KInt, I (S (S Z))])])])|  is accepted by the compiler
although it does not represent any family of datatypes. 

A direct solution to this problem is to introduce yet another index, this
time in the |Atom| datatype, which specifies which indices are allowed.
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
\texttt{\nameofourlibrary} becomes useless to them.
\item The choice of opaque types might be too wide. If we try to encompass any
possible situation, we might end up with a huge |Atom| type. But for a
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

  In the remainder of this section we wish to showcase a selection of particularly
powerful combinators that are simple to define by exploiting the
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
opaque types and another for mapping over |I| positions.

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

  This definition |zipRep| can be translated  to work with an arbitrary
|(Alternative f)| instead of |Maybe|. The |compos|
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
is to show that \texttt{\nameofourlibrary} is at least as powerful as any other comparable
library, but brings in the union of their advantages. 
Note also that even though some examples use a single recursive
datatype for the sake of conciseness, those can be readily generalized to
mutually recursive families.

There are many other applications for generic programming which
greatly benefit from supporting mutual recursion, if not requiring it.
One great source of examples consists of operations on abstract syntax
trees of realistic languages, such as generic
diffing~\cite{CacciariMiraldo2017} or
pretty-printing~\cite{Magalhaes2010}.

\subsection{Equality}

\begin{figure}
\begin{myhs}
\begin{code}
geq  ::  (Family kappa fam codes) 
     =>  (forall k dot kappa k -> kappa k -> Bool)
     ->  El fam ix -> El fam ix -> Bool
geq eq_K x y = go (deepFrom x) (deepFrom y)
  where
    go :: Fix codes ix -> Fix codes ix -> Bool
    go (Fix x) (Fix y)  = maybe False (elimRep (uncurry eq_K) (uncurry go) and) 
                        $ zipRep x y  
\end{code} %$
\end{myhs}
\caption{Generic equality}
\label{fig:genericeq}
\end{figure}

  As usually done on generic programming papers,
we should define generic equality in our own framework. 
In fact, with \texttt{\nameofourlibrary} we can define a particularly
elegant version of generic equality, given in \Cref{fig:genericeq}.

  Reading through the code we see that we convert both
arguments of |geq| to their deep representation, then compare their
top level constructor with |zipRep|. If they agree
we go through each of their fields calling either the equality on
opaque types |eq_K| or recursing.

\subsection{$\alpha$-Equivalence}
\label{sec:alphaequivalence}

A more involved exercise is the definition of
\emph{$\alpha$-equivalence} for a language
defined as a Haskell datatype.
On this section we start by
showing a straightforward version for the $\lambda$-calculus and then move
on to a more elaborate language. Although such problem has already been treated
using generic programming~\cite{Weirich2011}, it provides a good
example to illustrate our library. 

  Regardless of the language, determining whether two programs are
$\alpha$-equivalent requires one to focus on the constructors that
introduce scoping, declare variables or reference variables. All the
other constructors of the language should just
combine the recursive results. Let us warm up with the
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

  Let us explain the process step by step. First, for |t_1, t_2 :: LambdaTerm|
to be $\alpha$-equivalent, they have to have the constructors
on the same positions. Otherwise, they cannot be
$\alpha$-equivalent. Then we check the bound variables: we 
traverse both terms at the same time and
every time we go through a binder, in this case |Abs|, we register a
new \emph{rule} saying that the bound variable names are equivalent
for the terms under that scope. Whenever we find a reference to a
variable, |Var|, we check if the referenced variable is 
equivalent under the registered \emph{rules} so far.

  Let us abstract away this book-keeping functionality by the means of
a monad with a couple of associated functions. The idea is that monad |m| will
keep track of a stack of scopes, and each scope will register a list
of \emph{name-equivalences}. Indeed, this is very close to how one
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
of |v_1| and |v_2| in the top of the scope stack. Finally, |v_1 =~= v_2| is defined
by pattern matching on the scope stack. If the stack is empty, then |(=~=) v_1 v_2 = (v_1 == v_2)|.
Otherwise, let the stack be |s:ss|. We first traverse |s| gathering the rules
referencing either |v_1| or |v_2|. If there are none, we check if |v_1 =~= v_2| under |ss|.
If there are rules referencing either variable name in the topmost stack, we must
ensure there is only one such rule, and it states a name equivalence between |v_1| and |v_2|.
We will not show the implementation of these functions as these can be checked in 
the \texttt{Examples} directory of \texttt{\nameofourlibrary}. We implemented
them for the |MonadAlphaEq (State [[ (String , String) ]])| instance. 

\begin{figure}
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
\caption{$\alpha$-equivalence for a $\lambda$-calculus}
\label{fig:alphalambda}
\end{figure}

  Returning to our main focus and leaving book-keeping functionality
aside, we define in \Cref{fig:alphalambda} our alpha equivalence decision procedure by encoding what to do
for |Var| and |Abs| constructors. The |App| can be eliminated generically.

  There is a number of remarks to be made for this example. First,
note the application of |zipRep|. If two |LambdaTerm|s are made with different
constructors, |galphaEq| will already return |False| because |zipRep| will fail.
When |zipRep| succeeds though, we get access to one constructor with
paired fields inside. The |go| is then responsible for performing
the necessary semantic actions for the |Var| and |Abs|
constructors and applying a general eliminator for anything else.
In the actual library, the \emph{pattern synonyms} |(Pat LambdaTerm)|, |(Pat Var)|,
 and |(Pat Abs)| are automatically 
generated as we will see in \Cref{sec:templatehaskell}.

  One might be inclined to believe that the generic programming here
is more cumbersome than a straightforward pattern matching definition
over |LambdaTerm|. If we consider a more intricate language,
however, manual pattern matching becomes almost intractable
very fast.

Take the toy imperative language defined in \Cref{fig:alphatoy}.
$\alpha$-equivalence for this language can be defined with just a 
couple of changes to the definition for |LambdaTerm|.
For one thing, |alhaEq|, |step| and |galphaEq| remain the same.  We just need to
adapt the |go| function. Here writing
$\alpha$-equivalence by pattern matching is not straightforward anymore.
Moreover, if we decide to change this language and
add more statements or more expressions, the changes to the |go|
function are minimal, none if we do not introduce any additional construct
which declares or uses variables. As long as we do not touch the
constructors that |go| patterns matches on, we can even use the very same
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
\caption{$\alpha$-quivalence for a toy imperative language}
\label{fig:alphatoy}
\end{figure}

\subsection{The Generic Zipper}

  To conclude our examples section we will conduct a validation
exercise involving a more complex application of generic
programming. Zippers~\cite{Huet1997} are a well established technique
for traversing a recursive data structure keeping track of the current
\emph{focus point}. Defining generic zippers is nothing new, this has
been done by many authors~\cite{Hinze2004,Adams2010,Yakushev2009} for
many different classes of types in the past. To the best of the
authors knowledge, this is the first definition in a direct
\emph{sums-of-products} style.  We will not be explaining what
\emph{are} zippers in detail, instead, we will give a quick reminder
and show how zippers fit within our framework.

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

  In our case, this location type consists of a distinguished element
of the family |El fam ix| and a stack of contexts with a hole of type |ix|, where
we can plug in the distinguished element. This stack of contexts may build
a value whose type is a different member of the family; we recall its index
as |iy|. 

For the sake of conciseness we present the datatypes for a fixed interpretation
of opaque types |ki :: kon -> Star|, a family |fam ::
[Star]| and its associated codes |codes :: [[[Atom kon]]]|.
In the actual implementation all those elements appear as additional
parameters to |Loc| and |Ctxs|.

\begin{myhs}
\begin{code}
data Loc :: Nat -> Star where
  Loc :: El fam iy -> Ctxs ix iy -> Loc ix
\end{code}
\end{myhs}

  The second field of |Loc|, the stack of contexts,
represents how deep into the recursive
tree we have descended so far. Each time we unwrap another layer of recursion,
we push some context onto the stack to be able to go back up. Note how
the |Cons| constructor resembles some sort of composition operation.

\begin{myhs}
\begin{code}
data Ctxs :: Nat -> Nat -> Star where
  Nil   :: Ctxs ix ix
  Cons  :: Ctx (Lkup codes iz) iy -> Ctxs ix iz -> Ctxs ix iy
\end{code}
\end{myhs}

  Each element in this stack is an individual context, |Ctx c iy|.
A context is defined by a choice of a constructor
for the code |c|, paired a product of the correct type where one 
of the elements is a hole. This hole represents where the distinguished element
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

  The navigation functions are a direct translation of those defined 
for the \texttt{multirec}~\cite{Yakushev2009} library, that use the
|first|, |fill|, and |next| primitives for working over |Ctx|s.
The |fill| function can be taken over almost unchanged, whereas |first| and |next| require
a simple trick: we have to wrap the |Nat| parameter of |NPHole| in an
existential in order to manipulate it conveniently. The |ix| is packed up in an existential
type since we do not really know beforehand which member of the mutually
recursive family is seen first in an arbitrary product.

\begin{myhs}
\begin{code}
data NPHoleE :: [Atom kon] -> Star where
  Witness :: El fam ix -> NPHole c ix -> NPHoleE c
\end{code}
\end{myhs}

  Now we can define the |firstE| and |nextE|, the counterparts of
|first| and |next| from \texttt{multirec}. Intuitively,
|firstE| returns the |NPHole| with the 
first recursive position (if any) selected, |nextE| tries to find the
next recursive position in an |NPHole|. These functions have the following types:

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
of the type |LambdaTerm| defined in \Cref{sec:alphaequivalence}.
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
account of the generic zipper.
In fact, we were able to provide the same zipper interface 
as the \texttt{multirec} library. Our implementation is shorter, however.
This is because we do not need type classes to implement |firstE| and |nextE|.

\

  In this section we have shown several recurring examples from the
generic programming community. Using \texttt{\nameofourlibrary} we can have
both expressive power and convenience.
%  The overall selection of examples show that by keeping the good ideas from
%the generic programming community and putting them all under the same roof
%we are able to achieve powerful functionality in a convenient fashion.
  The last point we have to address is that we still have to write
the |Family| instance for the types we want to use. For instance,
the |Family| instance for example in \Cref{fig:alphatoy} is not going
to be fun. Deriving these automatically is possible, but non-trivial,
as we shall see in \Cref{sec:templatehaskell} 

\section{Template Haskell}
\label{sec:templatehaskell}

  Having a convenient and robust way to get the |Family| instance for
a given selection of datatypes is paramount for the usability of our
library. In a real scenario, a mutually recursive family
may consist of many datatypes with dozens of
constructors. Sometimes these datatypes are written with parameters,
or come from external libraries.

Our goal is to automate the generation of |Family| instances under all
those circumstances using \emph{Template Haskell}~\cite{Sheard2002}.
From the programmers' point of view, they only need to call |deriveFamily|
with the topmost (that is, the first) type of the family. For example:

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

  The |deriveFamily| takes care of unfoldinf the (type level) recursion until it
reaches a fixpoint.  In this case, the |type FamProgString = P [Prog
String , dots]| will be generated, together with its |Family|
instance. Optionally, one can also pass along a custom function to decide
whether a type should be considered opaque. By default, it uses a
selection of Haskell built-in types as opaque types.

\subsection{Unfolding the Family}
\label{sec:underthehood}

  The process of deriving a whole mutually recursive family from a single
member is conceptually divided into two disjoint process. First we unfold all definitions
and follow all the recursive paths until we reach a fixpoint. At that moment
we know that we
have discovered all the types in the family. Second, we translate the definition
of those types to the format our library expects.
During the unfolding process we keep a key-value map in a 
|State| monad, keeping track of the types we have seen, the types we have
seen \emph{and} processed and the indices of those within the family.

  Let us illustrate this process in a bit more detail using our running example
of a
mutually recursive family and consider through what
happens within \emph{Template Haskell} when it starts unfolding 
the |deriveFamily| clause.

\begin{myhs}
\begin{code}
data Rose a  = Fork a [Rose a]
data [a]     = nil | a : [a]

deriveFamily (tht (Rose Int))
\end{code}
\end{myhs}

  The first thing that happens is registering that we seen the type |Rose Int|.
Since it is the first type to be discovered, it is assigned index zero
within the family.
Next we need to reify the definition of |Rose|. At this point,
we query \emph{Template Haskell} for the definition, and we obtain
|data Rose x = Fork x [Rose x]|. Since |Rose| has kind |Star -> Star|, it cannot
be directly translated -- our library only supports ground types, which
are those with kind |Star|.
But we do not need a generic definition for |Rose|, we just need the specific case where |x = Int|.
Essentially, we just apply the reified definition of |Rose| to |Int| and $\beta$-reduce it,
giving us |Fork Int [Rose Int]|.

The next processing step is looking into
the types of the fields of the (single) constructor |Fork|. First we see |Int| and
decide it is an opaque type, say |KInt|. Second, we see |[Rose Int]| and
notice it is the first time we see this type. Hence, we register it with a fresh
index, |S Z| in this case. The final result for |Rose Int| is |P [P [K KInt, I (S Z)]]|.

We now go into |[Rose Int]| for processing.
Once again we need to perform some amount of $\beta$-reduction
at the type level before inspecting its fields.
The rest of the process is the same that for |Rose Int|.
However, when we encounter the field of type |Rose Int| this is already
registered, so we just need to use the index |Z| in that position.

  The final step is generating the actual Haskell code from the data obtained
in the previous process. This is a very
verbose and mechanical process, whose details we
omit. In short, we generate the necessary type synonyms, pattern synonyms,
the |Family| instance, and metadata information.  The generated type
synonyms are named after the topmost type of the family, passed to
|deriveFamily|:

\begin{myhs}
\begin{code}
type FamRoseInt    = P [ Rose Int                    , [Rose Int] ]
type CodesRoseInt  = P [ (P [P [K KInt , I (S Z)]])  , P [ P [] , P [I Z , I (S Z) ] ] ]
\end{code}
\end{myhs}

  Pattern synonyms are useful for convenient pattern matching and injecting into
the |View| datatype. We produce two different kinds of pattern synonyms.
First, synonyms for generic representations, one per constructor. Second,
synonyms which associate each type in the recursive family with their
position in the list of codes.

\begin{myhs}
%format forkP = "\HT{\overline{Fork}}" 
%format nilP  = "\HT{\overbar{[]}}" 
%format consP = "\HT{\overline{:}}" 
\begin{code}
pattern forkP x xs  = Tag SZ       (NA_K x :* NA_I xs :* NP0)
pattern nilP        = Tag SZ       NP0
pattern x consP xs  = Tag (SS SZ)  (NA_I x :* NA_I xs :* NP0)

pattern (Pat RoseInt)      = SZ
pattern (Pat ListRoseInt)  = SS SZ
\end{code}
\end{myhs}

  The actual |Family| instance is exactly as the one shown in \Cref{sec:family}

\begin{myhs}
\begin{code}
instance Family Singl FamRoseInt CodesRoseInt where dots
\end{code}
\end{myhs}

%  Finally, we also generate some metadata to correlate
%the name of constructors and types with the generic representation. 
%We handle metadata almost entirely like \texttt{generics-sop}, with a 
%few differences that will be explained in \Cref{sec:metadata}

\subsection{Metadata}
\label{sec:metadata}

  The representations described up to now are enough to write generic equalities
and zippers. But there is one missing ingredient to derive generic
pretty-printing or conversion to JSON, for instance. We need to maintain
the \emph{metadata} information of our datatypes.
This metadata includes the datatype name, the module where it was defined,
and the name of the constructors. Without this
information you cannot write a function which outputs the string
\begin{verbatim}
Fork 1 [Fork 2 [], Fork 3 []]
\end{verbatim}
for a call to |genericShow (Fork 1 [Fork 2 [], Fork 3 []])|. The reason is that
the code of |Rose Int| does not contain the information that the constructor
of |Rose| is called |"Fork"|.

  Like in \texttt{generics-sop}~\cite{deVries2014}, having the code
for a family of datatypes available allows for a completely separate
treatment of metadata. This is yet another advantage of the
sum-of-products approach when compared to the more traditional pattern
functors. In fact, our handling of metadata is heavily inspired from
\texttt{generics-sop}, so much so that we will start by explaining a simplified version of
their handling of metadata, and then outline the differences to our approach. 

  The general idea is to store the meta information following the structure of
the datatype itself. So, instead of data, we keep track of the names of the
different parts and other meta information that can be useful. It is advantageous
to keep metadata separate from the generic representation as it would only
clutter the definition of generic functionality.

\begin{myhs}
\begin{code}
data DatatypeInfo :: [[Star]] -> Star where
  ADT  :: ModuleName -> DatatypeName -> NP  ConstructorInfo cs       -> DatatypeInfo cs
  New  :: ModuleName -> DatatypeName ->     ConstructorInfo (P [c])  -> DatatypeInfo (P [ P [ c ]])
\end{code}
\end{myhs}
\begin{myhs}
\begin{code}
data ConstructorInfo :: [Star] -> Star where
  Constructor  :: ConstructorName                             -> ConstructorInfo xs
  Infix        :: ConstructorName -> Associativity -> Fixity  -> ConstructorInfo (P [ x, y ])
  Record       :: ConstructorName -> NP FieldInfo xs          -> ConstructorInfo xs
\end{code}
\end{myhs}
\begin{myhs}
\begin{code}
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
data DatatypeInfo     :: [  [  Atom kon ]]  -> Star where ...
data ConstructorInfo  ::    [  Atom kon ]   -> Star where ...
data FieldInfo        ::       Atom kon     -> Star where ...
\end{code}
\end{myhs}

As we have discussed above, our library is able to generate codes not only
for single types of kind |Star|, like |Int| or |Bool|, but also for types which
are the result of type level applications, such as |Rose Int| and |[Rose Int]|.
The shape of the metadata information in |DatatypeInfo|, a module name plus
a datatype name, is not enough to handle these cases. 
We replace the uses of |ModuleName| and |DatatypeName| in 
|DatatypeInfo| by a richer promoted type |TypeName|, which can
describe applications, as required.
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
                    $  (Constructor "Fork") :* NP0
\end{code} %$
\end{myhs}

Once all the metadata is in place, we can use it in the same fashion
as \texttt{generics-sop}. We refer the interested reader to
\citet{deVries2014} for examples.
  

\section{Conclusion and Future Work}

  Generic programming is an ever changing field. The more the
Haskell language evolves, the more interesting generic programming
libraries we can create. Indeed, some of the language extensions we require 
in our work were not available at the time that some of the
libraries in the related work were developed.  

  Future work involves expanding the universe of datatypes that our
library can handle. Currently, every type involved in a recursive
family must be a ground type (of kind |Star| in Haskell terms); our
Template Haskell derivations acknowledges this fact by implementing
some amount of reduction for types.  This limits the functions we can
implement generically, for example we cannot write a generic |fmap|
function, since it operates on types of kind |Star -> Star|.
\texttt{GHC.Generics} supports type constructors with exactly one
argument via the \texttt{Generic1} type class. We foresee most of the
complexity to be in the definition of |Atom|, as it must support some
kind of application of type constructors to other parameters or opaque
types.

  The original sum-of-products approach does not handle all the ground
types either, only regular ones~\cite{deVries2014}. We inherit this
restriction, and cannot represent recursive families which involve
existentials or GADTs. The problem in this case is representing the
constraints that each constructor imposes on the type arguments.

  Our \texttt{\nameofourlibrary} is a powerful library for generic
programming that combines the advantages of previous approaches to
generic programming. We have carefully blended the information about
(mutually) recursive positions, from \texttt{multirec}, with the
sums-of-products codes, from \texttt{generics-sop}, maintaining the
advantages of both. The Haskell programmer is now able to use
simple, combinator-based generic programming for a more expressive
class of types than \texttt{generics-sop} allows. This is
interesting, especially since mutually recursive types were hard 
to handle in a generic fashion previous to \texttt{\nameofourlibrary}.
