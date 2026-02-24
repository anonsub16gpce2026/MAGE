\DocumentMetadata{}
\documentclass[10pt,sigplan,screen,review,anonymous]{acmart}

\setcopyright{none}
\settopmatter{printacmref=false}
\renewcommand\footnotetextcopyrightpermission[1]{}

%\usepackage{minted}
\usepackage[many]{tcolorbox}
\tcbuselibrary{minted,skins}
%\usepackage{minted}

\definecolor{Gray}{gray}{0.9}
\AtBeginDocument{%
  \providecommand\BibTeX{{%
    \normalfont B\kern-0.5em{\scshape i\kern-0.25em b}\kern-0.8em\TeX}}}

\newtcblisting{code}[1][haskell]{
  colback=Gray,
  listing engine=minted,
  minted language=#1,
  listing only,
  skin=tile,
  width=0.45\textwidth
 }
\BeforeBeginEnvironment{code}{\begin{table}[htp]}
\AfterEndEnvironment{code}{\end{table}}

\copyrightyear{2022}
\acmYear{2022}
\acmDOI{XXXXXXX.XXXXXXX}

%% These commands are for a PROCEEDINGS abstract or paper.
\acmConference[Conference acronym 'XX]{Make sure to enter the correct
  conference title from your rights confirmation emai}{June 03--05,
  2018}{Woodstock, NY}
%
%  Uncomment \acmBooktitle if th title of the proceedings is different
%  from ``Proceedings of ...''!
%
%\acmBooktitle{Woodstock '18: ACM Symposium on Neural Gaze Detection,
%  June 03--05, 2018, Woodstock, NY} 
\acmPrice{15.00}
\acmISBN{978-1-4503-XXXX-X/18/06}

\begin{document}

\title{{\tt MAGE}: A Modular Attribute Grammar Embedding}
\subtitle{Tackling the Expression Problem with a type-safe EDSL}

\author{Juan García-Garland}
\email{jpgarcia@fing.edu.uy}
\orcid{}
\affiliation{%
  \institution{Instituto de Computación}
  \city{Montevideo}
  \country{Uruguay}
}


%%
%% By default, the full list of authors will be used in the page
%% headers. Often, this list is too long, and will overlap
%% other information printed in the page headers. This command allows
%% the author to define a more concise list
%% of authors' names for this purpose.
\renewcommand{\shortauthors}{García-Garland et al.}
\newcommand\mage{{\tt MAGE}}
\begin{abstract}
We present \mage{}, a domain-specific language embedded in Haskell for
the definition of modular attribute grammars. \mage allows grammars to
be defined as first-class entities at the type level. A collection of
typed combinators is provided to construct computation rules, whose
well-formedness is statically enforced.

The typing discipline is based on a clear and explicit formalism,
which we delineate in the paper and reflect directly in the encoding.
We provide an implementation of extensible algebraic data types
parametrized by grammars, enabling modular extension of syntax.
Generic semantic functions are derived from a grammar and its
associated syntax, implementing the corresponding traversals.
\end{abstract}

\begin{CCSXML}
<ccs2012>
 <concept>
  <concept_id>10010520.10010553.10010562</concept_id>
  <concept_desc>Computer systems organization~Embedded systems</concept_desc>
  <concept_significance>500</concept_significance>
 </concept>
 <concept>
  <concept_id>10010520.10010575.10010755</concept_id>
  <concept_desc>Computer systems organization~Redundancy</concept_desc>
  <concept_significance>300</concept_significance>
 </concept>
 <concept>
  <concept_id>10010520.10010553.10010554</concept_id>
  <concept_desc>Computer systems organization~Robotics</concept_desc>
  <concept_significance>100</concept_significance>
 </concept>
 <concept>
  <concept_id>10003033.10003083.10003095</concept_id>
  <concept_desc>Networks~Network reliability</concept_desc>
  <concept_significance>100</concept_significance>
 </concept>
</ccs2012>
\end{CCSXML}

\ccsdesc[500]{Computer systems organization~Embedded systems}
\ccsdesc[300]{Computer systems organization~Redundancy}
\ccsdesc{Computer systems organization~Robotics}
\ccsdesc[100]{Networks~Network reliability}

%%
%% Keywords. The author(s) should pick words that accurately describe
%% the work being presented. Separate the keywords with commas.
\keywords{datasets, neural networks, gaze detection, text tagging}

\received{20 February 2007}
\received[revised]{12 March 2009}
\received[accepted]{5 June 2009}

%%
%% This command processes the author and affiliation and title
%% information and builds the first part of the formatted document.
\maketitle

\section{Introduction}
\subsection{Description of our Problem}

\section{Library Overview}
\subsection{Defining Syntax}
\subsection{Representing Syntax}
\subsection{Defining Semantics}
\subsection{Extending Syntax}
\subsection{Extending Semantics}

\section{Abstract Type System}

\section{Implementation}

\section{Discussion}

\section{Related Work}


\end{document}
\endinput
%%
%% End of file `sample-sigconf.tex'.
