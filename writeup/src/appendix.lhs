\appendix

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
reaches a fixpoint.  In this case, the type synonym |FamProgString = P [Prog
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
type  FamRoseInt
      = P [ Rose Int                    , [Rose Int] ]
type  CodesRoseInt
      = P [ (P [P [K KInt , I (S Z)]])  , P [ P [] , P [I Z , I (S Z) ] ] ]
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

\section{Metadata}
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
This information is tied to a datatype by means of an additional type class
|HasDatatypeInfo|.
Generic functions may now query the metadata by means of functions like
|datatypeName|, which reflect the type information into the term level.
The definitions are given in \Cref{fig:sopmeta}.

\begin{figure*}
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

class HasDatatypeInfo a where
  datatypeInfo :: proxy a -> DatatypeInfo (Code a)
\end{code}
\end{myhs}
\caption{Definitions related to metadata from \texttt{generics-sop}}
\label{fig:sopmeta}
\end{figure*}


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
  ADT  ::  TypeName  -> NP  ConstructorInfo cs
       ->  DatatypeInfo cs
  New  ::  TypeName  ->     ConstructorInfo (P [c])
       ->  DatatypeInfo (P [ P [ c ]])
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
class  (Family kappa fam codes)
       =>  HasDatatypeInfo kappa fam codes ix 
       |   fam -> kappa codes where
  datatypeInfo  ::  (ix ~ Idx ty fam , Lkup ix fam ~ ty)
                =>  Proxy fam -> Proxy ty
                ->  DatatypeInfo (Lkup ix codes)
\end{code}
\end{myhs}

  The Template Haskell will then generate something similar to
the instance below for the first type in the family, |Rose Int|:

\begin{myhs}
\begin{code}
instance HasDatatypeInfo Singl FamRose CodesRose Z where
  datatypeInfo _ _ 
    =  ADT (ConT "E" "Rose" :@: ConT "Prelude" "Int")
    $  (Constructor "Fork") :* NP0
\end{code} %$
\end{myhs}

Once all the metadata is in place, we can use it in the same fashion
as \texttt{generics-sop}. We refer the interested reader to
\citet{deVries2014} for examples.