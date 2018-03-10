%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%
%% Recommended by the ACM ppl
\usepackage{booktabs}
\usepackage{subcaption}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%
%% Our packages
\usepackage{xcolor}
\usepackage{booktabs}
\usepackage{forest}

%% Cleveref must be the last loaded package
%% since it modifies the cross-ref system.
\usepackage{cleveref}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%
%% Our defs

%% More space between rows
\newcommand{\ra}[1]{\renewcommand{\arraystretch}{#1}}

%% Logistic Stuff

\definecolor{C1}{RGB}{0,153,204}
\definecolor{C2}{RGB}{89,0,179}

\newcounter{commentctr}[section]
\setcounter{commentctr}{0}
\renewcommand{\thecommentctr}{%
\arabic{section}.\arabic{commentctr}}

\newcommand{\warnme}[1]{%
{\color{red} \textbf{$[$} #1 \textbf{$]$}}}

\newcommand{\TODO}[1]{%
{\color{purple} \textbf{$[$ TODO: } #1 \textbf{$]$}}}

\newcommand{\tmp}[1]{%
{\color{gray} \textit{#1} }}

\newenvironment{temp}{\bgroup \color{gray} \textit}{\egroup}

\newcommand{\alejandro}[2][nolabel]{%
{\color{C1} \refstepcounter{commentctr}\label{#1} \textbf{$[$ (\thecommentctr) Alejandro: } #2 \textbf{$]$}}}
\newcommand{\victor}[2][nolabel]{%
{\color{C2} \refstepcounter{commentctr}\label{#1} \textbf{$[$ (\thecommentctr) Victor: } #2 \textbf{$]$}}}

%% LaTeX stuff

\newenvironment{myhs}{\par\vspace{0.15cm}\begin{minipage}{\textwidth}}{\end{minipage}\vspace{0.15cm}}


\newcommand{\nameofourlibrary}{generic-mrsop}


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%
%% lhs2TeX Formatting Rules
%%
%include stylish.lhs
%%

% Easy to typeset Haskell types using the \HSCon
% command from stylish.lhs (if it's defined!)
\newcommand{\HT}[1]{\ifdefined\HSCon\HSCon{#1}\else#1\fi}
\newcommand{\HS}[1]{\ifdefined\HSSym\HSSym{#1}\else#1\fi}
\newcommand{\HV}[1]{\ifdefined\HSVar\HSVar{#1}\else#1\fi}

%%% Datatype Promotion
%format (P (a)) = "\HS{''}" a

%%% Pattern Synonyms
\newcommand{\overbar}[1]{\mkern 1.5mu\overline{\mkern-1.5mu#1\mkern-1.5mu}\mkern 1.5mu}
%format (Pat a) = "\HT{\overbar{" a "}}"

%%% Usefull Notation
%format dots    = "\HS{\dots}"
%format forall  = "\HS{\forall}"
%format dot     = "\HS{.}"
%format ^=      = "\HS{\bumpeq}"
%format alpha   = "\HV{\alpha}"
%format phi     = "\HV{\varphi}"
%format phi1    = "\HV{\varphi_1}"
%format phi2    = "\HV{\varphi_2}"
%format kappa   = "\HV{\kappa}"
%format kappa1  = "\HV{\kappa_1}"
%format kappa2  = "\HV{\kappa_2}"
%format fSq     = "\HV{f}"
%format =~=     = "\HS{\approx}"

%%% Types
%format GenericGen = "\HT{\textit{Generic}_{\mathsf{gen}}}"
%format GenericSOP = "\HT{\textit{Generic}_{\mathsf{sop}}}"
%format GenericFix = "\HT{\textit{Generic}_{\mathsf{fix}}}"
%format RepGen     = "\HT{\textit{Rep}_{\mathsf{gen}}}"
%format RepSOP     = "\HT{\textit{Rep}_{\mathsf{sop}}}"
%format RepFix     = "\HT{\textit{Rep}_{\mathsf{fix}}}"
%format RepMRec    = "\HT{\textit{Rep}_{\mathsf{mrec}}}"
%format CodeSOP    = "\HT{\textit{Code}_{\mathsf{sop}}}"
%format CodeFix    = "\HT{\textit{Code}_{\mathsf{fix}}}"
%format CodeMRec   = "\HT{\textit{Code}_{\mathsf{mrec}}}"
%format NPHole     = "\HT{NP_{\square}}"
%format NPHoleE    = "\HT{\exists NP_{\square}}"
%format Tag        = "\HT{\textit{Tag}}"


%%% Functions
%format from     = "\HV{\textit{from}}"
%format fromGen  = "\HV{\textit{from}_{\mathsf{gen}}}"
%format fromSOP  = "\HV{\textit{from}_{\mathsf{sop}}}"
%format fromFix  = "\HV{\textit{from}_{\mathsf{fix}}}"
%format fromMRec = "\HV{\textit{from}_{\mathsf{mrec}}}"
%format toGen    = "\HV{\textit{to}_{\mathsf{gen}}}"
%format toSOP    = "\HV{\textit{to}_{\mathsf{sop}}}"
%format toFix    = "\HV{\textit{to}_{\mathsf{fix}}}"
%format toMRec   = "\HV{\textit{to}_{\mathsf{mrec}}}"
%format firstE   = "\HV{first_\exists}"
%format nextE    = "\HV{next_\exists}"
%format fam      = "\HV{\mathit{fam}}"
%format fmap     = "\HV{\textit{fmap}}"
%format fold     = "\HV{\textit{fold}}"

%format :>: = "\HT{\triangleright}"
%format :*  = "\HT{\times}"
%format :*: = "\HT{:\!*\!:}"
%format :+: = "\HT{:\!+\!:}"
%format :@: = "\HT{:\!@\!:}"
%format <$$> = "\HS{<\!\!\$\!\!>}"
%format $$  = "\HS{\$}"
%format <*> = "\HS{<\!\!*\!\!>}"

%format <-> = "\HS{\leftrightarrow}"

%format NilRoseTree = "\HS{[]_{\mathsf{RoseTree}}}"
%format ConsRoseTree = "\HS{\mathrel{:_{\mathsf{RoseTree}}}}"