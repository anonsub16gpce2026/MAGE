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
We present \mage{} (Modular Attribute Grammar Embedding), a
domain-specific language embedded in Haskell for the definition of
modular attribute grammars. \mage{} allows grammars to be defined as
first-class entities at the type level. A collection of typed
combinators is provided to construct computation rules, whose
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

\tableofcontents

\section{INTRODUCTION}

The Expression Problem (EP)~\cite{ExpressionProblem} is a classical
formulation concerning the expressiveness of programming languages and
their support for modular extensibility. It asks how to define a family
of data types together with a family of operations over them in such a
way that both dimensions can be extended independently, without
modifying existing code and while preserving static type safety.

In its standard presentation, the problem highlights a well-known
tension between data-oriented and operation-oriented decomposition.

Functional languages typically allow new operations to be added
modularly, but extending the underlying data types requires revisiting
existing definitions. In contrast, object-oriented languages support
the modular addition of new data variants, while making it difficult to
add new operations without modifying existing classes.

Beyond this classical formulation, stronger versions of the EP require
that extensions be separately type-checked and compiled, ensuring true
modular compilation.

Attribute Grammars (AGs) have been proposed as a formalism to address
the Expression Problem~\cite{REF}. By separating syntax from semantic
computations, AGs offer a structured mechanism to extend languages
along both dimensions. In practice, however, existing systems often
resolve the problem only at the level of user pragmatics: although
extensions can be expressed modularly, previously defined components
are frequently reprocessed or globally re-type-checked. This
limitation is not accidental. Well-formedness of an AG is determined
by global criteria, and enforcing these criteria typically requires
whole-grammar analysis.

Type-level programming refers to the practice of programming within
the type system code that will ``run'' at compile time. This allows
the encoding of expressive properties at the type level that must be
satisfied by the corresponding code at the value level. Type-level
programming techniques allow programmers to simulate dependent types
in a type system where types and terms mantain their level
independence. This allows type inference can be mantained at some
extend, at the cost of using some very particular pragmatics.

Embedded domain-specific languages (EDSLs) are languages defined within
a host language. Their main advantage is that they reuse the existing
toolchain of the host, avoiding the need to implement parsers,
type-checkers, or compilers from scratch. At the same time, they can
exploit all the facilities of the host language, including its type
system and support for modular compilation.

In this paper we introduce \mage{}, a library for representing AGs in
Haskell, aimed at addressing the Expression Problem in its strong
formulation. \mage{} uses type-level programming to encode a static
well-formedness discipline for AGs. This discipline is defined formally
in~\cite{REF}, and we provide an overview of its main ideas in
Section~\ref{sec:typesystem}.

\newpage

\section{PRELIMINARIES}

In this section we define...

\subsection{Attribute Grammars}\label{sec:typesystem}

Attribute grammars (AGs) are a formalism that equips context-free
grammars (CFGs) with semantics. This is achieved by associating
attributes to grammar symbols (both terminals and non-terminals) and
by defining rules that compute the attribute values in terms of the
attributes of parent and child nodes in the abstract syntax tree
(AST).

Formally, an AG is a tuple $(G, A, R)$, consisting of a CFG $G$, a set
of attributes $A$, and a set of semantic rules $R$. Attributes can be
inherited or synthesized, and each grammar symbol has a set of
inherited and synthesized attributes, so to completely specify $A$, we
give sets $I(X), S(X)$ for each grammar symbol $X$.

Consider the following example:

\[
\begin{array}{lcc|l}
E &\rightarrow& E_l + E_r
\quad
&\{\, E.\mathit{eval} := E_l.\mathit{eval} + E_r.\mathit{eval}, \\
&&& \qquad E_r.\mathit{env} := E.\mathit{env}, \\
&&& \qquad E_l.\mathit{env} := E.\mathit{env} \,\}
\\[0.5em]
E &\rightarrow& \mathcal{V}
\quad
&\{\, E.\mathit{eval} := E.\mathit{env}(\mathcal{V}.\mathit{val}) \,\}
\end{array}
\]
\hrule
\[
\begin{array}{cc}
S(E) = \{\mathit{eval}\},& I(E) = \{\mathit{env}\} \\
S(+) = \emptyset,& I(+) = \emptyset  \\
S(\mathcal{V}) = \{\mathit{val}\},& I(\mathcal{V}) =\emptyset
\end{array}
\]


On the left-hand side we have a CFG with two productions describing a
language of arithmetic expressions with variables and addition (such
as \texttt{"x"} or \texttt{"x + y"}). The symbol $E$ is a
non-terminal, while \texttt{+} and $\mathcal{V}$ are terminals. On the
right-hand side we present the semantic rules $R$ associated with each
production.

In this grammar we consider the attribute set \hfill\break
$A = \{\mathit{eval}, \mathit{env}, \mathit{val}\}$. Terminal symbols
do not require computation rules for inherited attributes;
$\mathit{val}$ denotes the concrete value of a variable, represented as
a string.

The attribute $\mathit{env}$ represents an environment mapping
variables to values. It is propagated along the AST towards the leaves.
In the first production, the second and third semantic equations
specify this propagation. We say that $\mathit{env}$ is an inherited
attribute, since it flows from parent to children in the AST (from left
to right according to the production).

The attribute $\mathit{eval}$, of type integer, denotes the semantic
value of the expression. In the first production it is computed as a
function of the $\mathit{eval}$ attributes of the children.

In the second production, the environment is accessed directly:
$E.\mathit{env}(V.\mathit{val})$ denotes the lookup of the key
$V.\mathit{val}$ in the environment $E.\mathit{env}$. We say that
$\mathit{eval}$ is a synthesized attribute, since it flows from the
children towards the parent in the AST (from right to left in the
production).

An AG is \emph{well-formed} whenever attribute evaluation can be
performed in any an AST of the grammar. This is classically reduced to
two conditions:

\begin{itemize}
\item Well-definedness: There is exacly one rule at every production,
  to compute every required attribute.
\item Non-circularity: for each AST there is a scheduling to compute
  the attribute occurrences [TODO] DEFINE so no computation depends on
  an uncomputed occurrence.
\end{itemize}

When non-strict semantics are used the non-circularity condition can
be dropped since we could have circular definitions still
productive. That is our context for the DSL, so we concentrate on
well-definedness. 

To show why AGs are a proposed solution to the EP, in the example
above, we may enrich the grammar with additional semantics by
introducing a new attribute together with its associated rules. For
instance, by adding rules $\{E.\mathit{size} := E_l.\mathit{size} +
E_r.\mathit{size} + 1\}$ and $\{E.\mathit{size} := 1\}$ for each
production, respectively, we equip the language with a semantics that
computes the size of each expression.

Orthogonally, we may extend the original grammar with new syntax. For
example, to enrich the language of expressions with a null constant, it
suffices to add a new production together with its corresponding
semantic rule:

\[
E \rightarrow 0
\qquad
\{\, E.\mathit{eval} := 0 \,\}
\]

The local nature of rules with respect to productions allow us to
define new semantics without referring to the previous
definitions........

However, to decide whether a full AG is well-formed

\subsubsection{A type system for Attribute Grammars}

\subsection{Type-level programming in Haskell}

\subsection{The expression Problem}

The challenge is to devise an implementation technique that satisfies
the following requirements~\cite{REF}:

\begin{itemize}
  \item \textbf{Extensibility in both dimensions.}
  It must be possible to introduce new data variants and adapt existing
  operations accordingly. Dually, it must be possible to define new
  processors over previously defined data.

  \item \textbf{Strong static type safety.}
  It should be impossible to apply a processor to a data variant that
  it does not handle. All mismatches must be detected statically.

  \item \textbf{No modification or duplication.}
  Existing definitions should neither be modified nor duplicated when
  extensions are introduced.

  \item \textbf{Separate compilation.}
  Extending the datatype or adding new processors should not require
  re-type-checking previously compiled components. In particular, no
  safety checks should be deferred to linking or runtime.

  \item \textbf{Independent extensibility.}
  Independently developed extensions should be composable and usable
  jointly without additional adaptation.
\end{itemize}


\newpage

\section{LIBRARY OVERVIEW}

In this section we present an overview of the library. The purpose is
to give the reader a concrete understanding of how \mage{} is used in
practice and how it addresses the Expression Problem. Each subsection
is presented as a literate Haskell module, implemented as an
independent file, each one independently compilable.

\subsection{Defining Syntax}


\subsection{Representing Syntax}

\subsection{Defining Semantics}

\subsection{Extending Syntax}

\subsection{Extending Semantics}

\subsection{Discussion}
\newpage

\section{IMPLEMENTATION}

\newpage

\section{DISCUSSION}

\section{RELATED WORK}

\bibliographystyle{plain}
\bibliography{biblio}


\end{document}
\endinput
%%
%% End of file `sample-sigconf.tex'.
