\section{Introduction}
\label{sec:introduction}

Generic programming provides mechanisms to implement functions
on the shape of a datatype. A well-known example is the |deriving| mechanism
in Haskell, which frees the programmer from writing repetitive functions such as
equality~\cite{haskell2010}. Work on this type of genericity 
\victor{Should we mention there are other types of genericty? IF so, it's either
here or in the abstract} is especially
prolific in Haskell, where a vast range of approaches are available as
preprocessors, language extensions, or
libraries~\cite{Rodriguez2008,Magalhaes2012}. Generic programming has become a
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
for the second if contains two subtrees as children. In fact, |Bin a|
is isomorphic to the |Either a (Bin a , Bin a)| type. 
\victor{I feel we should add a paragraph with our final |gsize| function here;
tell that story of ``oh, what if we change the datatype'' and capitalize
on the neat definition}
\tmp{
In order to represent this datatype generically, we need to remember that:
\begin{enumerate}
\item A value of |Bin a| can be built using one of two constructors;
\item If you use the first constructor you hold a value of the type |a|;
\item On the other hand, a value built using |Bin| contains two subtrees as
children.
\end{enumerate}
}
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
This type is isomorphic to |Either a (Bin a , Bin a)|, but using the combinators
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

\victor{perhaps instead of equality we show |gsize|?}
Once you have a uniform description language for datatypes, generic code
is merely code that operates under this uniform language, ie:
\begin{myhs}
\begin{code}
eq x y = genericEq (from x) (from y)
\end{code}
\end{myhs}
The |genericEq| function operates at the level of descriptions:
\begin{enumerate}
\item Checks whether |x| and |y| are built from the same constructor, in
negative case we can already return |False|;
\item If they both share the constructor, equality is checked for every pair
of children of |x| and |y|.
\end{enumerate}

\paragraph{Deep versus shallow.}
\victor{Does it really showcase? This sentence is misleading}
This simple function already showcases the difference between \emph{shallow}
and \emph{deep} representation of datatypes. When using a shallow representation
only one layer of the value is turned into a generic form by a call to |from|.
As a result, our |genericEq| needs to call |from| again over each childre
 before going recursively into then.
This is the kind of representation we get from \texttt{GHC.Generics}, among
others.

The other side of the spectrum are \emph{deep} representation, in which the
entire value is turned into the set of combinators the generic library provides
in one go. Since you have the entire shape of the value under your hands, you can
use deep representation to transform the datatype; for example, you can define
the type of regular expressions over a datatype~\cite{Serrano2016}\victor{confusing}. In the case
of generic equality, using a deep description implies that only call to
|from| is needed, but it traverses the value completely. This poses a
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
declare which fields you have. \victor{These sentence reminded me of containers} However, this shape is \emph{not enforced} at
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
We call the \emph{representation} the functor that gives semantic to \emph{codes},
if any. Some generic programming libraries define only \emph{representation}.
\tmp{
At this point we remark the relation between a \emph{representation} -- like
|RepGen| -- and a \emph{code} -- like |CodeSOP|.
Both are examples of descriptions of a datatype, but operate at different
levels. Representations are type constructors, functor more specifically,
whereas codes are aggregations of ground types (a list of lists in the case
of |CodeSOP|). This means that we can build a value using the type of the
representation, whereas we need to perform an additional step in the case of
codes. For example, \texttt{generics-sop} defines a type family |RepSOP| which
converts from a code into a representation. Manipulating codes instead of
representation leads to a simpler style of generic programming.
}

\paragraph{Mutually recursive datatypes.}

We have described several axis taken by different approaches to generic
programming in Haskell. Unfortunately, most of the works restrict themselves
to \emph{regular} types, in which recursion always goes to the \emph{same}
datatype. This is not enough for some practical applications. For example,
HTML and XML documents are better described by a rose tree, which is a mutually 
recursive family of datatypes:
\begin{myhs}
\begin{code}
data RoseTree  a  =  a :>: [RoseTree a]
data []        a  =  [] | a : [a]
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
\victor{if it already received treatment, why are we mentioning it? Perhaps
mention the previous treatment on the $\alpha$-eq section, this is confusing.}
Usual problems such as $\alpha$-equality have received a treatment using generic
programming~\cite{Weirich2011}. It is natural to ask how to extend those
approaches when more than one datatype enters the game.

\victor{both multirec and regular provide a shallow encoding; but support deep}
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

\victor{I don't think we should go into this detail here; we can mention there
is a challenge we will address on a lter section}
There is an interesting problem that arises when we have mutually recursive
datatypes. The definition of |RoseTree a| above uses the list type, but not
simply |[a]|, but the specific instance |[RoseTree a]|. This means that the
procedure to derive the code must take into account this fact, effectively
spiting out the code for the following isomorphic type:
\begin{myhs}
\begin{code}
data RoseTree      a  =  a :>: RoseTreeList a
data RoseTreeList  a  =  NilRoseTree | RoseTree a ConsRoseTree RoseTreeList a
\end{code}
\end{myhs}
Shallow descriptions do not suffer too much from this problem. For deep
approaches, though, how to solve this problem is key to derive a useful
description of the datatype.

\subsection{Contributions}

\victor{How about selling it as a framework for keeping the
good stuff of each GP library? The moment we say we are presenting yet
another library prople might go ``oh well''}
In this paper we present \texttt{\nameofourlibrary}, a new library for generic
programming over mutually recursive families, which uses the sum-of-products
approach. In particular we make the following contributions:

\begin{itemize}
\item We describe a technique to derive both deep and shallow encodings
of a datatype from a unified code (\Cref{sec:explicitfix}). This give users to
our library control over which style of generic programming they prefer in each
different scenario.
\item We extend the sum-of-products approach of \citet{deVries2014} to handle
mutually recursive families of datatypes (\Cref{sec:family}).
\item Codes and conversions to and from generic representations are
derived using Template Haskell (\Cref{sec:templatehaskell}).
The novelty lies in our handling of instantiated type constructors.
\item We use our generic programming approach to asbtract common patterns
such as equality, $\alpha$-equivalence and zipper (\Cref{sec:mrecexamples}).
\end{itemize}
Thoughout the text we compare our design to other approaches in the literature.