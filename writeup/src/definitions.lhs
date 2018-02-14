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

\newcommand{\alejandro}[1]{%
{\color{C1} \refstepcounter{commentctr} \textbf{$[$ (\thecommentctr) Alejandro: } #1 \textbf{$]$}}}
\newcommand{\victor}[1]{%
{\color{C2} \refstepcounter{commentctr} \textbf{$[$ (\thecommentctr) Victor: } #1 \textbf{$]$}}}

%% LaTeX stuff

\newenvironment{myhs}%
{\vspace{0.6em}\hspace{1em}}%
{\vspace{0.6em}}


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%
%% lhs2TeX Formatting Rules

%format fib = "\mathcal{F}"