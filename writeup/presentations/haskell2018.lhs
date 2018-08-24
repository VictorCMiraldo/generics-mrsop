\documentclass{beamer}

\usetheme{uucs}

%include polycode.fmt 

% ---------------------------------------------------

\title{Generic Programming of All Kinds}
\author{Alejandro Serrano Mena, Victor Cacciari Miraldo}
\date{February 28, 2018}

\begin{document}

\begin{frame}
  \titlepage
\end{frame}

\begin{frame}
  \frametitle{generics-sop}

  start on |NS| and |NP|

  ppl might not be familiar with this black magic!

  show |gsize|!
\end{frame}

\begin{frame}
  \frametitle{Enlarging the language of types!}

  show figure 2!

  examples!
\end{frame}

\begin{frame}
  \frametitle{Applying type-level types to types!}

  Show |Ty|, and how it interprets |Atom| into a star for us.

  Show the |Generic| type-class and mention the existence of |ApplyT|
  and why you need such monster

\end{frame}

\begin{frame}
  \frametitle{Wait?! type-in-type?}

\end{frame}

\begin{frame}
  \frametitle{Constraints}

\end{frame}

\begin{frame}
  \frametitle{Generic GADT}


  limitations: |forall k (a :: k)| can't be represented by us
\end{frame}

\begin{frame}
  \frametitle{Arity-generic fmap }

\end{frame}


\begin{frame}
  \frametitle{Lessons discussion and conc}

  \begin{itemize}
    \item Existentials are not a problem; check paper
    \item Explicit recursion is not a problem unless you take fixpoints; check the paper
    \item Mutual recursion? No biggie! MRSOP!
  \end{itemize}

  Conclusion: We rock!

\end{frame}

\begin{frame}
  \titlepage
\end{frame}

\end{document}