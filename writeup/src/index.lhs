\documentclass[screen,sigplan]{acmart}%
\settopmatter{printfolios=true,printccs=true,printacmref=true}

%%%%%%%%%%%%%%
%%%%%%%%%%%%%%
%% Template 

%%% The following is specific to TyDe '18 and the paper
%%% 'Sums of Products for Mutually Recursive Datatypes'
%%% by Victor Cacciari Miraldo and Alejandro Serrano.
%%%
\setcopyright{acmlicensed}
\acmPrice{15.00}
\acmDOI{10.1145/3240719.3241786}
\acmYear{2018}
\copyrightyear{2018}
\acmISBN{978-1-4503-5825-5/18/09}
\acmConference[TyDe '18]{Proceedings of the 3rd ACM SIGPLAN International Workshop on Type-Driven Development}{September 27, 2018}{St. Louis, MO, USA}
\acmBooktitle{Proceedings of the 3rd ACM SIGPLAN International Workshop on Type-Driven Development (TyDe '18), September 27, 2018, St. Louis, MO, USA}

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

\usepackage{multirow}
\usepackage{balance}

\begin{document}

%% Title information
\title[Sums of Products for Mutually Recursive Datatypes]{Sums of Products for Mutually Recursive Datatypes}
%\titlenote{with title note}
\subtitle{The Appropriationist's View on Generic Programming}
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
  %\position{PhD candidate}
  \department{Information and Computing Sciences}
  \institution{Utrecht University}
  \streetaddress{Princetonplein, 5}
  \city{Utrecht}
  %\state{Utrecht}
  \postcode{3584 CC}
  \country{The Netherlands} 
}
\email{V.CacciariMiraldo@@uu.nl}

\author{Alejandro Serrano}
\affiliation{
  %\position{Junior lecturer}
  \department{Information and Computing Sciences}
  \institution{Utrecht University}
  \streetaddress{Princetonplein, 5}
  \city{Utrecht}
  %\state{Utrecht}
  \postcode{3584 CC}
  \country{The Netherlands} 
}
\email{A.SerranoMena@@uu.nl}


%% Abstract
%% Note: \begin{abstract}...\end{abstract} environment must come
%% before \maketitle command
\begin{abstract} 
  Generic programming for mutually recursive families
of datatypes is hard.
On the other hand, most interesting abstract syntax trees
are described by a mutually recursive family of datatypes.
We could give up on using that mutually
recursive structure, but then we lose the ability to use
those generic operations which take advantage of that
same structure. We present a new approach to generic programming that uses
modern Haskell features to handle mutually recursive families with
explicit \emph{sum-of-products} structure. This additional structure allows
us to remove much of the complexity previously associated with generic
programming over these types.
\end{abstract}


%% 2012 ACM Computing Classification System (CSS) concepts
%% Generate at 'http://dl.acm.org/ccs/ccs.cfm'.
\begin{CCSXML}
<ccs2012>
<concept>
<concept_id>10011007.10011006.10011008.10011009.10011012</concept_id>
<concept_desc>Software and its engineering~Functional languages</concept_desc>
<concept_significance>500</concept_significance>
</concept>
<concept>
<concept_id>10011007.10011006.10011008.10011024.10011028</concept_id>
<concept_desc>Software and its engineering~Data types and structures</concept_desc>
<concept_significance>500</concept_significance>
</concept>
</ccs2012>
\end{CCSXML}

\ccsdesc[500]{Software and its engineering~Functional languages}
\ccsdesc[500]{Software and its engineering~Data types and structures}
%% End of generated code


%% Keywords
%% comma separated list
\keywords{Generic Programming, Datatype, Haskell}


%% \maketitle
%% Note: \maketitle command must come after title commands, author
%% commands, abstract environment, Computing Classification System
%% environment and commands, and keywords command.
\maketitle

\balance
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
% \newpage
\bibliography{references}


%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%
%
% Appendix
%
\newpage
%include src/appendix.lhs
%
%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%

\end{document}
