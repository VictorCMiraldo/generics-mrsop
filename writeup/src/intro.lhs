\section{Introduction}
\label{sec:introduction}

\emph{(Datatype-)generic programming} provides mechanisms to implement functions
on the shape of a datatype~\cite{Gibbons2006}. A well-known example is the |deriving| mechanism
in Haskell, which frees the programmer from writing repetitive functions such as
equality~\cite{haskell2010}. A vast range of approaches are available as
preprocessors, language extensions, or
libraries for Haskell~\cite{Rodriguez2008,Magalhaes2012}. In fact, generic programming has become a
common technique in the programmers' toolbox. A library like Scrap Your
Boilerplate~\cite{Lammel2003} has 275 reverse dependencies at the time of
writing.\footnote{As reported by
\url{https://packdeps.haskellers.com/reverse/syb}.} Popular libraries like
Aeson, the de facto standard for JSON serialization in Haskell, use generic
programming even in their tutorials.\footnote{Documentation at 
\url{hackage.haskell.org/package/aeson/docs/Data-Aeson.html}.}

The core underlying idea of generic programming is the fact that a great
number of datatypes can be described in a uniform fashion.
Consider the following datatype representing binary trees with data at their
leaves:
\begin{myhs}
\begin{code}
data Bin a = Leaf a | Bin (Bin a) (Bin a)
\end{code}
\end{myhs}
A value of type |Bin a| consists of a choice between two constructors.
For the first choice, it also constains a value of type |a| whereas 
for the second if contains two subtrees as children. This means that the |Bin a| type
is isomorphic to |Either a (Bin a , Bin a)|. 

Different libraries differ on how they define their underlying generic descriptions. 
For example,
\texttt{GHC.Generics}~\cite{Magalhaes2010} defines the representation of |Bin|
as the following datatype:\footnote{Throughout this paper we use subscripts
to distinguish the generic programming library at hand.}
\begin{myhs}
\begin{code}
RepGen (Bin a) = K1 R a :+: (K1 R (Bin a) :*: K1 R (Bin a))
\end{code}
\end{myhs}
which is a direct translation of |Either a (Bin a , Bin a)|, but using the combinators
provided by \texttt{GHC.Generics}, namely |:+:| and |:*:|. In addition, we need
two conversion functions |from :: a -> Rep a x| and |to :: Rep a x -> a|
which form an isomorphism
between |Bin a| and |RepGen (Bin a) x|.\footnote{The additional type argument
to |RepGen| can be ignored for the moment. Its role shall become clear once
we introduce pattern functors in \Cref{sec:patternfunctors}.}
All this information is tied to the
original datatype using a type class:
\begin{myhs}
\begin{code}
class Generic a where
  type RepGen a :: * -> *
  fromGen  :: a -> RepGen a x
  toGen    :: RepGen a x -> a
\end{code}
\end{myhs}
Most generic programming libraries
follow a similar pattern of defining the \emph{description} of
a datatype in the provided uniform language by some type-level information, 
and two functions witnessing an isomorphism. One important feature
of each library is how is this description encoded and which are the primitive
operations for constructing such encodings, since they ultimately define which
datatypes go under its cover.

Once you have a uniform description language for datatypes, generic code
is merely code that operates under this uniform language. One of the simplest
examples of generic programming is the definition of a |size|, akin to
|length| for lists of |leaves| for trees.

\begin{myhs}
\begin{code}
size x = genericSize (from x)
  where genericSize = crush (const 1) sum
\end{code}
\end{myhs}
The |from| function, defined above, translates the concrete value |x| into
the generic description language. The |crush (const 1) sum| function operates then at
that level: it recurses down potential children, and sum up the results. In fact, 
this is the very definition one can write using our framework, without any
added sugar, but we will get back to it in \Cref{sec:explicitfix}. For the rest
of the intro, let us get a small taste of the nuances between the different
design choices we will be exploring throughtout this paper.

\paragraph{Deep versus shallow.}
There are two ways to implement |from|, leading to different implementation
strategies for functions like |genericSize|. When using a \emph{shallow} representation
only one layer of the value is turned into a generic form by a call to |from|.
As a result, our |genericSize| needs to call |from| again over each children
 before going recursively into then.
This is the kind of representation we get from \texttt{GHC.Generics}, among
others.

The other side of the spectrum are \emph{deep} representation, in which the
entire value is turned into the representation that the generic library provides
in one go. \victor{I don't get the next sentence} Since you know the entire shape of the datatype, including when
recursion is places, deep techniques usually allow transformation of the
datatype, not only generic functionality. This additional power has been used,
for example, to define regular expressions over Haskell datatypes~\cite{Serrano2016}.
Depending on the use case, a shallow representation might be more efficient
if only part of the value needs to be inspected. On the other hand, deep
representations are sometimes easier to use, since the conversion is taken
care in one go. This poses a
trade-off between deep and shallow.

In general, descriptions that support a deep representation are more involved
than those that support only a shallow representation. The reason is that you need a way
to mark \emph{recursive} positions in your
datatype. In our |Bin| example, the description of the |Bin| constructor
changes from ``this constructors has two fields of the |Bin a| type'' to 
``this constructor has two fields in which you recurse''. The usual technique
is to abstract the recursion into a \emph{fixed-point} combinator. The
\texttt{regular} library~\cite{Noort2008}, for instance, supports this feature.

\paragraph{Sum of Products}

Most generic programming libraries build their type-level descriptions out of three basic
combinators: (1) \emph{constants}, which indicate a type which should appear
as-is; (2) \emph{products} (usually written as |:*:|) which are used to
build tuples; and (3) \emph{sums} (usually written as |:+:|) which
encode the choice between constructors. |RepGen (Bin a)| above is expressed in
this form.

In practice, you always use a sum of products to represent a datatype -- a sum
to express the choice of constructor, and within each of them a product to
declare which fields you have. However, this shape is \emph{not enforced} at
any level. A recent approach to generic programming~\cite{deVries2014}
explicitly uses a list of lists of types, the outer one representing the sum
and each inner one thought as products. The $\HS{'}$ sign in the code below marks the
list as operating in the type-level, as opposed to term-level lists which exists
at run-time. This is an example of Haskell's \emph{datatype} promotion~
\cite{Yorgey2012}.
\begin{myhs}
\begin{code}
CodeSOP (Bin a) = P [ P [a], P [Bin a, Bin a] ]
\end{code}
\end{myhs}
The shape of this description follows more closely the shape of Haskell datatypes, and
make it easier to implement generic functionality.

  Note how the \emph{code}, |CodeSOP (Bin a)| is another entity that is added
to ensure the \emph{representation} has a given structure. This is quite
a subtle point and it is common to see both terms being used interchangeably.
Being very precise, we call the \emph{representation} the functor that gives semantic 
to \emph{codes}, if any. Some generic programming libraries define only \emph{representation}.

\paragraph{Mutually recursive datatypes.}

We have described several axis taken by different approaches to generic
programming in Haskell. Unfortunately, most of the works restrict themselves
to \emph{regular} types, in which recursion always goes to the \emph{same}
datatype. This is not enough for some practical applications. For example,
HTML and XML documents are better described by a rose tree, which is a mutually 
recursive family of datatypes:
\begin{myhs}
\begin{code}
data Rose  a  =  a :>: [Rose a]
data []    a  =  [] | a : [a]
\end{code}
\end{myhs}

The syntax of many programming languages is also expressed more naturally using
a mutually recursive family. Talking about Haskell itself, one of the 
possibilities of an expression is to be a |do| block, a |do| block itself is
composed by a list of statements which may include expressions.
\begin{myhs}
\begin{code}
data Expr  = ... | Do [Stmt] | ...
data Stmt  = Assign Var Expr | Let Var Expr
\end{code}
\end{myhs}
Usual problems such as $\alpha$-equality, although already treated using generic
programming~\cite{Weirich2011}, still creeps back up when more than one datatype enters the stage.

The \texttt{multirec} library~\cite{Yakushev2009} is a generalization of
\texttt{regular} which handles mutually recursive families. From \texttt{regular}
it inherits its approach using representations. 
Our work stems from the desire of having both the concise structure
that the sum-of-products \emph{codes} give to the \emph{representation} of data
and the information for recursive positions in a mutually recursive setting.

\paragraph{Deriving the representation.}

Generic programming alleaviates the problem of writing repetitive operations
such as equality or pretty-printing, which depend on the structure of the
datatype. But in order to do so, they still require the programmer to figure
out the right description and write conversion function |from| and |to| that type. This is
tedious, and also follows the shape of the type!

For that reason, most generic programming libraries also include some
automatic way of generating this boilerplate code. \texttt{GHC.Generics} is
embedded in the compiler, most others use Template Haskell~\cite{Sheard2002},
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
procedure to derive the code must take into account this fact.
Shallow descriptions do not suffer too much from this problem. For deep
approaches, though, how to solve this problem is key to derive a useful
description of the datatype.

\subsection{Contributions}

In this paper we make the following contributions:
\begin{itemize}
\item We describe a technique to derive both deep and shallow encodings
of a datatype from a unified code (\Cref{sec:explicitfix}). This gives
control over which style of generic programming one prefers in each
different scenario.
\item We extend the sum-of-products approach of \citet{deVries2014} to handle
mutually recursive families of datatypes (\Cref{sec:family}).
\item Codes and conversions to and from generic representations are
derived using Template Haskell (\Cref{sec:templatehaskell}).
The novelty lies in our handling of instantiated type constructors.
\item We use our generic programming approach to asbtract common patterns
such as equality, $\alpha$-equivalence and zipper (\Cref{sec:mrecexamples}).
\end{itemize}
We have packaged our results as a Haskell library, \texttt{\nameofourlibrary},
which supports mutually recursive families and uses the sum-of-products approach.
This library supersedes many other generic programming libraries,
including |Generic| from \texttt{GHC.Generics}~\cite{Magalhaes2010},
\texttt{regular}~\cite{Noort2008},
\texttt{multirec}~\cite{Yakushev2009},
and \texttt{generic-sop}~\cite{deVries2014}.