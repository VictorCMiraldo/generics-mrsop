\section{Introduction}
\label{sec:introduction}

Generic programming provides mechanisms to derive implementation of functions
from the shape of a datatype. A well-known example is the |deriving| mechanism
in Haskell, which frees the programmer from writing repetitive functions such as
equality~\cite{haskell2010}. Work on this type of genericity is especially
prolific in Haskell, where a vast range of approaches are available as
preprocessors, language extensions, or
libraries~\cite{Rodriguez2008,Magalhaes2012}. Generic programming has become a
common technique in the programmers' toolbox. A library like Scrap Your
Boilerplate~\cite{Lammel2003} has 275 reverse dependencies at the time of
writing.\footnote{As reported by
\url{https://packdeps.haskellers.com/reverse/syb}.} Popular libraries like
Aeson, the de facto standard for JSON serialization in Haskell, use generic
programming in their tutorials.\footnote{Documentation at 
\url{hackage.haskell.org/package/aeson/docs/Data-Aeson.html}.}

The core underlying idea of generic programming is the fact that a great
number of datatypes can be translated to a uniform representation. 
Consider the following datatype representing binary trees with data at their
leaves:
\begin{myhs}
\begin{code}
data Bin a = Leaf a | Bin (Bin a) (Bin a)
\end{code}
\end{myhs}
In order to represent this datatype generically, we need to remember that:
\begin{enumerate}
\item A value of |Bin a| can be built using one of two constructors;
\item If you use the first constructor you hold a value of the type |a|;
\item On the other hand, a value built using |Bin| contains two subtrees as
children.
\end{enumerate}
Different libraries differ on how to encode this information. For example,
\texttt{GHC.Generics}~\cite{Magalhaes2010} defines the representation of |Bin|
as the following datatype:
\begin{myhs}
\begin{code}
Rep (Bin a) = K1 R a :+: (K1 R (Bin a) :*: K1 R (Bin a))
\end{code}
\end{myhs}
(which is isomorphic to |Either a (Bin a , Bin a)|), along with conversion
function |from :: a -> Rep a| and |to :: Rep a -> a| which form an isomorphism
between |Bin a| and |Rep (Bin a)|. Actually, most generic programming libraries
use a similar pattern of defining the \emph{representation} or \emph{code} of
a datatype, and two functions witnessing an isomorphism. One important feature
of each library is which are the primitive operations for constructing codes,
since they define which datatypes go under its cover.

Once you have a uniform representation for datatypes, writing generic code
becomes the matter of writing code that operates under this representation.
Image you want to write an equality operation, you can define it generically as:
\begin{myhs}
\begin{code}
eq x y = genericEq (convert x) (convert y)
\end{code}
\end{myhs}
where |convert| moves the value into the uniform representation. The |genericEq|
function then:
\begin{enumerate}
\item Checks whether |x| and |y| are built from the same constructor, in
negative case we can already return |False|;
\item If they both share the constructor, equality is checked for every pair
of children of |x| and |y|.
\end{enumerate}

\paragraph{Deep versus shallow.}
This simple function already showcases the difference between \emph{shallow}
and \emph{deep} representations of codes. In a shallow representation only one
layer of the value is turned into a generic form. As a result, our |genericEq|
needs to call |convert| over each children before going recursively into then.
This is the kind of representation we get from \texttt{GHC.Generics}, among
others.

The other side of the spectrum is \emph{deep} representation, in which the
entire value is turned into the set of combinators the generic library provides
in one go. Since you have the entire shape of the value under your hands, you can
use deep representation to transform the datatype; for example, you can define
the type of regular expressions over a datatype~\cite{Serrano2016}. In the case
of generic equality, using a deep representation implies that only call to
|convert| is needed, but it traverses the value completely. This poses a
trade-off between deep and shallow representations.

Codes for deep representation need a larger set of combinators than shallow
ones. In particular, you need a way to mark \emph{recursive} positions in your
datatype. In our |Bin| example, the representation of the |Bin| constructor
changes from ``this constructors has two fields of the |Bin a| type'' to 
``this constructor has two fields in which you recurse''. The usual technique
is to abstract the recursion into a \emph{fixed-point} combinator. The
\texttt{regular} library~\cite{Noort2008} uses this kind of codes. 

\paragraph{Sum-of-products.}

Most generic programming libraries build representations out of three basic
combinators: (1) \emph{constants}, which indicate a type which should appear
as-is; (2) \emph{products} (usually written as |:*:|) which are used to
build tuples; and (3) \emph{sums} (usually written as |:+:|) which
encode the choice between constructors. |Rep (Bin a)| above is expressed in
this form.

In practice, you always use a sum of products to represent a datatype -- a sum
to express the choice of constructor, and within each of them a product to
declare which fields you have. However, this shape is \emph{not enforced} at
any level. A recent approach to generic programming~\cite{deVries2014}
explicitly uses a list of lists of types, the outer one representing the sum
and each inner one thought as products.\footnote{The |quote| sign marks the
list as operating in the type-level, as opposed to term-level lists which exists
at run-time. This is an example of Haskell's \emph{datatype} promotion~
\cite{Yorgey2012}.}
\begin{myhs}
\begin{code}
Rep (Bin a) = quote [ quote [a], quote [Bin a, Bin a] ]
\end{code}
\end{myhs}
This representation follows more closely the shape of Haskell datatypes, and
make it easier to implement some generic functionality like random generation
of values.

\paragraph{Mutually recursive datatypes.}

We have described several axes taken by different approaches to generic
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
Usual problems such as $\alpha$-equality have received a treatment using generic
programming~\cite{Weirich2011}. It is natural to ask how to extend those
approaches when more than one datatype enters the game.

The \texttt{multirec} library~\cite{Yakushev2009} is a generalization of
\texttt{regular} which handles mutually recursive families. From \texttt{regular}
it inherits its deep representation approach using combinators. As discussed
above, there are other choices -- shallow representations and sum-of-products --
with different trade-offs. Our work stems from the desire of having the nice
properties of sum-of-products in a mutually recursive setting.

\paragraph{Deriving the representation.}

Generic programming alleaviates the problem of writing repetitive operations
such as equality or pretty-printing, which depend on the structure of the
datatype. But in order to do so, they still require the programmer to figure
out the code and write conversion function from and to that type. This is
tedious, and also follows the shape of the type!

For that reason, most generic programming libraries also include some
functionality which writes that code automatically. \texttt{GHC.Generics} is
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
Shallow representations do not suffer too much from this problem. For deep
representations, though, how to solve this problem is key to derive a code.

\subsection{Contributions}

In this paper we present \texttt{\nameofourlibrary}, a new library for generic
programming over mutually recursive families, which uses the sum-of-products
approach to codes. In particular we make the following contributions:

\begin{itemize}
\item We describe a technique to derive both deep and shallow representations
of a datatype from a unified code (\Cref{sec:explicitfix}). This give users to
our library control over which style of generic programming they prefer in each
different scenario.
\item We extend the sum-of-products approach of \citet{deVries2014} to handle
mutually recursive families of datatypes (\Cref{sec:family}).
\item Codes and conversions to and from generic representations are
derived using Template Haskell (\Cref{sec:templatehaskell}).
The novelty lies in our handling of instantiated type constructors.
\end{itemize}
Throughout the text we introduce examples of functions defined using generic
programming, such as equality and $\alpha$-equivalence. We also compare our
design to other approaches in the literature.