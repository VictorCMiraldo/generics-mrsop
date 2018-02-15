%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%
%% Recommended by the ACM ppl
\usepackage{booktabs}
\usepackage{subcaption}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%
%% Our packages
\usepackage{xcolor}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%
%% Our defs

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

\newcommand{\alejandro}[2][nolabel]{%
{\color{C1} \refstepcounter{commentctr}\label{#1} \textbf{$[$ (\thecommentctr) Alejandro: } #2 \textbf{$]$}}}
\newcommand{\victor}[2][nolabel]{%
{\color{C2} \refstepcounter{commentctr}\label{#1} \textbf{$[$ (\thecommentctr) Victor: } #2 \textbf{$]$}}}

%% LaTeX stuff

\newenvironment{myhs}{}{}



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

%%% Datatype Promotion
%format (P (a)) = "\HS{''}" a

%%% Usefull Notation
%format dots    = "\HS{\cdots}"
%format forall  = "\HS{\forall}"
%format dot     = "\HS{.}"

%%% Types
%format RepGen  = "\HT{Rep_{gen}}"
%format RepSOP  = "\HT{Rep_{sop}}"
%format RepFix  = "\HT{Rep_{Fix}}"
%format CodeSOP = "\HT{Code_{sop}}"
%format CodeFix = "\HT{Code_{fix}}"

%format :*  = "\HS{\times}"
%format :*: = ":\!*\!:"
%format :+: = ":\!+\!:"