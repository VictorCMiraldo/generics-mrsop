\documentclass[acmsmall,10pt,review,anonymous]{acmart}%
\settopmatter{printfolios=true,printccs=false,printacmref=false}

%%%%%%%%%%%%%%
%%%%%%%%%%%%%%
%% Template 

%% Conference information
%% Supplied to authors by publisher for camera-ready submission;
%% use defaults for review submission.
\acmConference[PL'17]{ACM SIGPLAN Conference on Programming Languages}{January 01--03, 2017}{New York, NY, USA}
\acmYear{2017}
\acmISBN{} % \acmISBN{978-x-xxxx-xxxx-x/YY/MM}
\acmDOI{} % \acmDOI{10.1145/nnnnnnn.nnnnnnn}
\startPage{1}

%% Copyright information
%% Supplied to authors (based on authors' rights management selection;
%% see authors.acm.org) by publisher for camera-ready submission;
%% use 'none' for review submission.
\setcopyright{none}
%\setcopyright{acmcopyright}
%\setcopyright{acmlicensed}
%\setcopyright{rightsretained}
%\copyrightyear{2017}           %% If different from \acmYear

%% Bibliography style
\bibliographystyle{acmart/ACM-Reference-Format}
%% Citation style
%\citestyle{acmauthoryear}  %% For author/year citations
%\citestyle{acmnumeric}     %% For numeric citations
%\setcitestyle{nosort}      %% With 'acmnumeric', to disable automatic
                            %% sorting of references within a single citation;
                            %% e.g., \cite{Smith99,Carpenter05,Baker12}
                            %% rendered as [14,5,2] rather than [2,5,14].
%\setcitesyle{nocompress}   %% With 'acmnumeric', to disable automatic
                            %% compression of sequential references within a
                            %% single citation;
                            %% e.g., \cite{Baker12,Baker14,Baker16}
                            %% rendered as [2,3,4] rather than [2-4].


%% END TEMPLATE
%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%

%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%
%
% Our formatting rules and included packages.
%
%include lhs2TeX.fmt
%include src/definitions.lhs
%
%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%


\begin{document}

%% Title information
\title[Sums of Products for Mutually Recursive Datatypes]{Sums of Products for Mutually Recursive Datatypes}
%\titlenote{with title note}
\subtitle{An Appropriationistic View on Generic Programming}
%\subtitlenote{with subtitle note}


%% Author information
%% Contents and number of authors suppressed with 'anonymous'.
%% Each author should be introduced by \author, followed by
%% \authornote (optional), \orcid (optional), \affiliation, and
%% \email.
%% An author may have multiple affiliations and/or emails; repeat the
%% appropriate command.
%% Many elements are not rendered, but should be provided for metadata
%% extraction tools.

\author{Victor Cacciari Miraldo}
\orcid{nnnn-nnnn-nnnn-nnnn}             %% \orcid is optional
\affiliation{
  \position{PhD candidate}
  \department{Information and Computing Sciences}
  \institution{Utrecht University}
  \streetaddress{Princetonplein, 5}
  \city{Utrecht}
  \state{Utrecht}
  \postcode{3584 CC}
  \country{The Netherlands} 
}
\email{V.CacciariMiraldo@@uu.nl}

\author{Alejandro Serrano}
\orcid{nnnn-nnnn-nnnn-nnnn}             %% \orcid is optional
\affiliation{
  \position{Junior lecturer}
  \department{Information and Computing Sciences}
  \institution{Utrecht University}
  \streetaddress{Princetonplein, 5}
  \city{Utrecht}
  \state{Utrecht}
  \postcode{3584 CC}
  \country{The Netherlands} 
}
\email{A.SerranoMena@@uu.nl}


%% Abstract
%% Note: \begin{abstract}...\end{abstract} environment must come
%% before \maketitle command
\begin{abstract}
  The technique of writting programs that operate on a uniform
representation of class of datatypes, \emph{Generic Programming}, has
its expressivity bounded by the quality of the choice of
representation.  Each having different drawbacks altogether.  The
Haskell ecosystem has many different libraries, but none is cabaple of
handling mutually recursive types in a convenient and simple form.  We
present a library for type-safe generic programming with mutually
recursive families and explicit \emph{sums-of-products} structure. The
\emph{sums-of-products} structure allows for simple, combinator-based,
generic functions that operate on arbitrarily complex families of
datatypes, including those comming from external libraries. Furthermore,
the library supports both shallow and deep encodings, giving programmers
a wider range of choice for their generic functions.
\end{abstract}


%% 2012 ACM Computing Classification System (CSS) concepts
%% Generate at 'http://dl.acm.org/ccs/ccs.cfm'.
\begin{CCSXML}
<ccs2012>
<concept>
<concept_id>10011007.10011006.10011008</concept_id>
<concept_desc>Software and its engineering~General programming languages</concept_desc>
<concept_significance>500</concept_significance>
</concept>
<concept>
<concept_id>10003456.10003457.10003521.10003525</concept_id>
<concept_desc>Social and professional topics~History of programming languages</concept_desc>
<concept_significance>300</concept_significance>
</concept>
</ccs2012>
\end{CCSXML}

\ccsdesc[500]{Software and its engineering~General programming languages}
\ccsdesc[300]{Social and professional topics~History of programming languages}
%% End of generated code


%% Keywords
%% comma separated list
\keywords{Generic Programming, Datatype, Haskell}


%% \maketitle
%% Note: \maketitle command must come after title commands, author
%% commands, abstract environment, Computing Classification System
%% environment and commands, and keywords command.
\maketitle

%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%
%
% Body
%
%include src/body.lhs
%
%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%

%% Acknowledgments
%\begin{acks}                            %% acks environment is optional
                                        %% contents suppressed with 'anonymous'
  %% Commands \grantsponsor{<sponsorID>}{<name>}{<url>} and
  %% \grantnum[<url>]{<sponsorID>}{<number>} should be used to
  %% acknowledge financial support and will be used by metadata
  %% extraction tools.
%  This material is based upon work supported by the
%  \grantsponsor{GS100000001}{National Science
%    Foundation}{http://dx.doi.org/10.13039/100000001} under Grant
%  No.~\grantnum{GS100000001}{nnnnnnn} and Grant
%  No.~\grantnum{GS100000001}{mmmmmmm}.  Any opinions, findings, and
%  conclusions or recommendations expressed in this material are those
%  of the author and do not necessarily reflect the views of the
%  National Science Foundation.
%\end{acks}


%% Bibliography
\bibliography{references.bib}


%% Appendix
%% \appendix
%% \section{Appendix}
%% 
%% %include src/appendix.lhs

\end{document}
