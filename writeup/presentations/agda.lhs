\usepackage{xcolor}
\usepackage{amsmath}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Math symbols and notation

\newcommand{\deceq}{%
\mathrel{\overset{\makebox[0pt]{\mbox{\normalfont\tiny\sffamily ?}}}{=}}
}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Agda formatting stuff

%% Color declarations
% Aspect colours.
\definecolor{AgdaComment}                {HTML}{B22222}
\definecolor{AgdaKeyword}                {HTML}{CD6600}
\definecolor{AgdaString}                 {HTML}{B22222}
\definecolor{AgdaNumber}                 {HTML}{A020F0}
\definecolor{AgdaSymbol}                 {HTML}{404040}
\definecolor{AgdaPrimitiveType}          {HTML}{0000CD}
\definecolor{AgdaOperator}               {HTML}{000000}

% NameKind colours.
\definecolor{AgdaBound}                  {HTML}{000000}
\definecolor{AgdaInductiveConstructor}   {HTML}{008B00}
\definecolor{AgdaCoinductiveConstructor} {HTML}{8B7500}
\definecolor{AgdaDatatype}               {HTML}{0000CD}
\definecolor{AgdaField}                  {HTML}{EE1289}
\definecolor{AgdaFunction}               {HTML}{0000CD}
\definecolor{AgdaMacro}                  {HTML}{458B74}
\definecolor{AgdaModule}                 {HTML}{A020F0}
\definecolor{AgdaPostulate}              {HTML}{0000CD}
\definecolor{AgdaPrimitive}              {HTML}{0000CD}
\definecolor{AgdaRecord}                 {HTML}{0000CD}
\definecolor{AgdaArgument}               {HTML}{404040}

% Other aspect colours.
\definecolor{AgdaDottedPattern}          {HTML}{000000}
\definecolor{AgdaUnsolvedMeta}           {HTML}{FFFF00}
\definecolor{AgdaTerminationProblem}     {HTML}{FFA07A}
\definecolor{AgdaIncompletePattern}      {HTML}{F5DEB3}
\definecolor{AgdaError}                  {HTML}{FF0000}

% Misc.
\definecolor{AgdaHole}                   {HTML}{9DFF9D}

% ---------------------------------------------------------------------
% Font Decls.

\newcommand{\AgdaFontStyle}[1]{\textsf{#1}}
\newcommand{\AgdaKeywordFontStyle}[1]{\textsf{#1}}
\newcommand{\AgdaStringFontStyle}[1]{\texttt{#1}}
\newcommand{\AgdaCommentFontStyle}[1]{\texttt{#1}}
\newcommand{\AgdaBoundFontStyle}[1]{\textit{#1}}

% ----------------------------------------------------------------------
% Commands.

% Aspect commands.
\newcommand{\AgdaComment}     [1]
    {\AgdaCommentFontStyle{\textcolor{AgdaComment}{#1}}}
\newcommand{\AgdaKeyword}     [1]
    {\AgdaKeywordFontStyle{\textcolor{AgdaKeyword}{#1}}}
\newcommand{\AgdaString}      [1]{\AgdaStringFontStyle{\textcolor{AgdaString}{#1}}}
\newcommand{\AgdaNumber}      [1]{\AgdaFontStyle{\textcolor{AgdaNumber}{#1}}}
\newcommand{\AgdaSymbol}      [1]{\AgdaFontStyle{\textcolor{AgdaSymbol}{#1}}}
\newcommand{\AgdaPrimitiveType}[1]
    {\AgdaFontStyle{\textcolor{AgdaPrimitiveType}{#1}}}
\newcommand{\AgdaOperator}    [1]{\AgdaFontStyle{\textcolor{AgdaOperator}{#1}}}

% NameKind commands.
\newcommand{\AgdaNoSpaceMath}[1]
    {\begingroup\thickmuskip=0mu\medmuskip=0mu#1\endgroup}

\newcommand{\AgdaBound}[1]
    {\AgdaNoSpaceMath{\AgdaBoundFontStyle{\textcolor{AgdaBound}{#1}}}}
\newcommand{\AgdaInductiveConstructor}[1]
    {\AgdaNoSpaceMath{\AgdaFontStyle{\textcolor{AgdaInductiveConstructor}{#1}}}}
\newcommand{\AgdaCoinductiveConstructor}[1]
    {\AgdaNoSpaceMath{\AgdaFontStyle{\textcolor{AgdaCoinductiveConstructor}{#1}}}}
\newcommand{\AgdaDatatype}[1]
    {\AgdaNoSpaceMath{\AgdaFontStyle{\textcolor{AgdaDatatype}{#1}}}}
\newcommand{\AgdaField}[1]
    {\AgdaNoSpaceMath{\AgdaFontStyle{\textcolor{AgdaField}{#1}}}}
\newcommand{\AgdaFunction}[1]
    {\AgdaNoSpaceMath{\AgdaFontStyle{\textcolor{AgdaFunction}{#1}}}}
\newcommand{\AgdaMacro}[1]
    {\AgdaNoSpaceMath{\AgdaFontStyle{\textcolor{AgdaMacro}{#1}}}}
\newcommand{\AgdaModule}[1]
    {\AgdaNoSpaceMath{\AgdaFontStyle{\textcolor{AgdaModule}{#1}}}}
\newcommand{\AgdaPostulate}[1]
    {\AgdaNoSpaceMath{\AgdaFontStyle{\textcolor{AgdaPostulate}{#1}}}}
\newcommand{\AgdaPrimitive}[1]
    {\AgdaNoSpaceMath{\AgdaFontStyle{\textcolor{AgdaPrimitive}{#1}}}}
\newcommand{\AgdaRecord}[1]
    {\AgdaNoSpaceMath{\AgdaFontStyle{\textcolor{AgdaRecord}{#1}}}}
\newcommand{\AgdaArgument}[1]
    {\AgdaNoSpaceMath{\AgdaBoundFontStyle{\textcolor{AgdaArgument}{#1}}}}

% Other aspect commands.
\newcommand{\AgdaFixityOp}          [1]{\AgdaNoSpaceMath{$#1$}}
\newcommand{\AgdaDottedPattern}     [1]{\textcolor{AgdaDottedPattern}{#1}}
\newcommand{\AgdaUnsolvedMeta}      [1]
    {\AgdaFontStyle{\colorbox{AgdaUnsolvedMeta}{#1}}}
\newcommand{\AgdaTerminationProblem}[1]
    {\AgdaFontStyle{\colorbox{AgdaTerminationProblem}{#1}}}
\newcommand{\AgdaIncompletePattern} [1]{\colorbox{AgdaIncompletePattern}{#1}}
\newcommand{\AgdaError}             [1]
    {\AgdaFontStyle{\textcolor{AgdaError}{\underline{#1}}}}

% Misc.
\newcommand{\AgdaHole}[1]{\colorbox{AgdaHole}{#1}}
\long\def\AgdaHide#1{} % Used to hide code from LaTeX.

\newcommand{\AgdaIndent}[1]{$\;\;$}


%% Finally, our shortcuts

%% Agda color shortcuts
\newcommand{\D}[1]{\AgdaDatatype{#1}}
\newcommand{\F}[1]{\AgdaFunction{#1}}
\newcommand{\K}[1]{\AgdaKeyword{#1}}
\newcommand{\N}[1]{\AgdaSymbol{#1}}
\newcommand{\Nm}[1]{\AgdaSymbol{#1}}
\newcommand{\RF}[1]{\AgdaField{#1}}
\newcommand{\IC}[1]{\AgdaInductiveConstructor{#1}}
\newcommand{\ICArgs}[2]{\AgdaInductiveConstructor{#1}$\; #2 $}
\newcommand{\DArgs}[2]{\D{#1}$\; #2 $}

%% Agda keywords
%format data   = "\K{data}"
%format where  = "\K{where}"
%format record = "\K{record}"
%format field  = "\K{field}"
%format mutual = "\K{mutual}"
%format with   = "\K{with}"
%format module = "\K{module}"
%format let    = "\K{let}"
%format in     = "\K{in}"
%format if     = "\K{if}"
%format then   = "\K{then}"
%format else   = "\K{else}"

%% Agda standard types
%format Set    = "\F{Set}"
%format Set1   = "\F{Set$_1$}"
%format Nat    = "\F{$\mathbb{N}$}"
%format Bool   = "\F{Bool}"
%format List   = "\F{List}"
%format Vec    = "\F{Vec}"
%format Maybe  = "\F{Maybe}"
%format Fin    = "\F{Fin}"
%format Dec    = "\F{Dec}"
%format ==     = "\F{$\equiv$}"
%format =?=    = "\F{$\deceq$}"
%format =~=    = "\F{$\cong$}"
%format Unit   = "\F{Unit}"
%format flip   = "\F{flip}"
%format Bot    = "\F{$\bot$}"
%format All    = "\F{$All$}"
%format String = "\F{$String$}"
%format Sigma  = "\F{$\Sigma$}"
%format *      = "\F{$\times$}"
%format +      = "\F{$\uplus$}"

%% Constructors of the above types
%format ::       = "\hspace{.4em}\IC{:\hspace{-.5em}:}\hspace{.4em}"
%format []       = "\IC{[]}"
%format just     = "\IC{just}"
%format nothing  = "\IC{nothing}"
%format yes      = "\IC{yes}"
%format no       = "\IC{no}"
%format false    = "\IC{false}"
%format true     = "\IC{true}"
%format zero     = "\IC{zero}"
%format suc      = "\IC{suc}"
%format unit     = "\IC{tt}"
%format inj1     = "\IC{inj$_1$}"
%format inj2     = "\IC{inj$_2$}"
%format proj1    = "\RF{proj$_1$}"
%format proj2    = "\RF{proj$_2$}"

%% Some standard functions
%format lookup  = "\F{lookup}"
%format length  = "\F{length}"
%format map     = "\F{map}"
%format id      = "\F{id}"
%format return  = "\F{return}"
%format uncurry = "\F{uncurry}"
%format <$$>    = "\F{$<\hspace{-.1em}\$\hspace{-.1em}>$}"
%format <**>    = "\F{$<\hspace{-.1em}*\hspace{-.1em}>$}"
%format ++      = "\F{$++$}"
%format >>=     = "\F{$>>=$}"
%format Delta   = "\F{$\Delta$}"

%% Non-colored stuff
%format mapsto          = "\mapsto"
%format forall          = "\forall"
%format eta             = "\eta"
%format mu              = "\mu"
%format alpha           = "\alpha"
%format alpha_1         = "\alpha_1"
%format alpha_2         = "\alpha_2"
%format kappa           = "\kappa"
%format kappa_1         = "\kappa_1"
%format kappa_2         = "\kappa_2"
%format sigma           = "\sigma"
%format sigma_1         = "\sigma_1"
%format sigma_2         = "\sigma_2"
%format sigmas          = "{\sigma}s"
%format pi              = "\pi"
%format pi_1            = "\pi_1"
%format pi_2            = "\pi_2"
%format pis             = "{\pi}s"

%format (SPLIT (a) (b)) = "\langle {" a "} , {" b "} \rangle"

%% Useful symbols
%format cdots     = "\cdots"
%format holder    = "\cdot"
%format holderL   = "\hspace{-.1em}" holder
%format holderR   = holder "\hspace{-.1em}"
%format holderLR  = "\hspace{-.1em}" holder "\hspace{-.1em}"
