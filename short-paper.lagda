\pdfoutput=1 
\documentclass[a4paper, twocolumn]{article}
\usepackage[a4paper, margin=1in]{geometry}

\usepackage{tikz}
\usepackage[T1]{fontenc}
\usepackage{agda}

\begin{code}[hide]
module FlipperLAFI where

open import Prelude hiding (flip; uncurry)
\end{code}

\showboxdepth=\maxdimen
\showboxbreadth=\maxdimen

\usepackage[font=small,labelfont=bf]{caption}
\usepackage{j}
\usepackage{inconsolata}
\usepackage{stmaryrd}
\usepackage{graphicx}
\usepackage{polytable}
\newcommand{\rot}{\rotatebox[origin=B]{180}}

\evensidemargin -0.23in  
\oddsidemargin -0.23in 
\setlength\headheight{10pt}
\setlength\headsep{10pt}
\setlength\textwidth{6.75in}
\setlength\columnsep{0.25in}

% \bdiv is similar to \bmod
\DeclareRobustCommand\bdiv{%
  \nonscript\mskip-\medmuskip\mkern5mu%
  \mathbin{\operator@font div}\penalty900\mkern5mu%
  \nonscript\mskip-\medmuskip}

\usepackage{listings}
\lstset{
  basicstyle=\small\ttfamily,
  xleftmargin=10pt
}
\addbibresource{flipper.bib}
\DeclareUnicodeCharacter{05A8}{\dg}
\title{Verified Reversible Programming for
Verified Lossless Compression}

\author{James Townsend and Jan-Willem van de Meent\\
University of Amsterdam}

\date{}

\begin{document}

\maketitle

It has been known since the work of Claude Shannon in the late 1940s
that there is a deep connection between probabilistic modelling
and lossless data compression. In \cite{shannon1948}, Shannon showed
that the best achievable compressed size for random data is equal to
the expected negative log-probability, a quantity which he called the
`entropy'.  Practical approaches to lossless compression work by
assuming a model \(P\) over input data \(x\), and compressing \(x\) to
a size close to the negative log-probability \(-\log_2 P(x)\), using a
coding method such as Huffman coding \cite{huffman1952}, arithmetic
coding \cite{moffat1998}, or asymmetric numeral systems (ANS)
\cite{duda2009}.
Recently, a number of papers have shown that modern deep generative
models can be used to achieve state-of-the-art compression rates
\cite{townsend2019,%
kingma2019a,townsend2020,hoogeboom2019,berg2021,ruan2021,zhang2021,%
kingma2021}. These recent works all use ANS, a method which, due to
its simplicity and superior performance, has also become ubiquitous in
production compression systems.\footnote{A list is maintained at
\jurl{encode.su/threads/%
2078-List-of-Asymmetric-Numeral-Systems-implementations}, which
includes various ANS programs with state-of-the-art performance.}

Our work on this paper began with an observation: in ANS-based
methods, the encoder and decoder programs appear to have the same
structure.  Indeed, we realised that it made sense to view them as
different interpretations of \emph{the same} program, one `doing' the
program and the other `undoing' it. Following this idea to its logical
conclusion, we have implemented a small, \emph{reversible} domain
specific language, called Flipper, embedded in Agda \cite{norell2007},
via an Agda macro. The potential advantages of using Flipper are
significant---the amount of user code is reduced, and accidental
violation of the inverse property (a common cause of bugs in lossless
compression) is no longer possible.


Flipper programs inhabit an Agda record type:\footnote{
We would have preferred the names `do' and `undo' to `apply' and
`unapply', but unfortunately `do' is a reserved keyword in Agda.
}
%replace <->'    "\ensuremath{\leftrightarrow}"
%replace ≡       "\ensuremath{\equiv}"
%replace forall  "\ensuremath{\forall}"
\begin{code}
record _<->'_ (A B : Set) : Set where
  field
    apply : A -> B
    unapply : B -> A
    prfa : forall a -> unapply (apply a)   ≡ a
    prfb : forall b -> apply   (unapply b) ≡ b
\end{code}
The Flipper macro takes a user implementation of
\AgdaField{apply} in
\AgdaBound{A}
\AgdaSymbol{\ensuremath{\rightarrow}}
\AgdaBound{B},
and compiles it into an inhabitant of
\AgdaBound{A}
\AgdaFunction{\ensuremath{\leftrightarrow}}
\AgdaBound{B}, complete with an implementation of \AgdaField{unapply}
and the two necessary correctness proofs.

The compiler only accepts functions expressed in an `obviously'
reversible form, where the reverse interpretation can be seen by
literally rotating the source code by \(180^\circ\) (more detail on
this below). Despite this restriction on form, we have found Flipper
to be a surprisingly effective language for implementing lossless
compression, and surprisingly enjoyable to use. 

There is a tradition of `reversible' programming languages going back
at least as far as \cite{Lutz86}, and we took particular
inspiration from the pure functional reversible languages rFun
\cite{yokoyama2012,thomsen2015a} and Theseus \cite{james2014}. We believe
that Flipper is the first in this tradition to support dependent
types, and as far as we know the first to be formally verified. We
also think that embedding the reversible language in a well
established host language, with excellent editor integration, makes
writing software in Flipper significantly easier than existing
reversible languages. The power of these features is demonstrated by
our implementation of ANS-based compression in Flipper, which to our
knowledge is the most sophisticated compression method to have been
implemented in a reversible language to date.\footnote{We plan to
publicly release Flipper and the ANS compression implementation soon.}

\section{The Flipper language}
The Flipper compiler accepts an
\AgdaField{apply}\AgdaSpace{}%
\AgdaSymbol{:}\AgdaSpace{}%
\AgdaBound{A}\AgdaSpace{}%
\AgdaSymbol{\ensuremath{\rightarrow}}\AgdaSpace{}%
\AgdaBound{B},
expressed as a pattern-matching lambda term with a special
property: rotating the term by \(180^\circ\),
and ``re-righting'' any upside down symbols, results in a valid
term in 
\AgdaBound{B}\AgdaSpace{}%
\AgdaSymbol{\ensuremath{\rightarrow}}\AgdaSpace{}%
\AgdaBound{A}, which we can use as our \AgdaField{unapply}.
\begin{code}[hide]
open import Flipper
\end{code}

As a first example, consider the `flippable' function which swaps the
elements of a pair:
%replace <->    "\ensuremath{\leftrightarrow}"
\begin{code}
pair-swp : forall {A B} -> A × B <-> B × A
pair-swp = F \ { (a , b) -> (b , a) }
\end{code}
Here the Flipper compiler, \AgdaFunction{F}, is applied to a lambda
term. Flipping that term gives
\begin{center}
\rotatebox[origin=c]{180}{%
\AgdaSymbol{\ensuremath{\lambda}}\AgdaSpace{}%
\AgdaSymbol{\{}\AgdaSpace{}%
\AgdaSymbol{(}%
\AgdaBound{a}\AgdaSpace{}%
\AgdaInductiveConstructor{,}\AgdaSpace{}%
\AgdaBound{b}%
\AgdaSymbol{)}\AgdaSpace{}%
\AgdaSymbol{\ensuremath{\rightarrow}}\AgdaSpace{}%
\AgdaSymbol{(}%
\AgdaBound{b}\AgdaSpace{}%
\AgdaInductiveConstructor{,}\AgdaSpace{}%
\AgdaBound{a}%
\AgdaSymbol{)}\AgdaSpace{}%
\AgdaSymbol{\}}}.
\end{center}
Rerighting symbols (including the
\AgdaInductiveConstructor{\AgdaUnderscore{},\AgdaUnderscore{}}
constructor/pattern)
and moving the \AgdaSymbol{\ensuremath{\lambda}}
over to the left, we see that in this case
\begin{center}%
\AgdaField{unapply}\AgdaSpace{}%
\AgdaSymbol{\ensuremath{=}}\AgdaSpace{}%
\AgdaSymbol{\ensuremath{\lambda}}\AgdaSpace{}%
\AgdaSymbol{\{}\AgdaSpace{}%
\AgdaSymbol{(}%
\AgdaBound{b}\AgdaSpace{}%
\AgdaInductiveConstructor{,}\AgdaSpace{}%
\AgdaBound{a}%
\AgdaSymbol{)}\AgdaSpace{}%
\AgdaSymbol{\ensuremath{\rightarrow}}\AgdaSpace{}%
\AgdaSymbol{(}%
\AgdaBound{a}\AgdaSpace{}%
\AgdaInductiveConstructor{,}\AgdaSpace{}%
\AgdaBound{b}%
\AgdaSymbol{)}\AgdaSpace{}%
\AgdaSymbol{\}}.%
\end{center}

Note that, in order for the rotated \AgdaField{unapply} to be a valid
Agda function, it is necessary that each bound variable in a flippable
must be used exactly once.  To emphasize the view of \AgdaField{apply}
and \AgdaField{unapply} as different interpretations (or orientations)
of the same program, from here on we will use a more concise,
symmetrical syntax for flippable definitions:
%clean-flippables-on
\begin{code}[hide]
variable
  A B C X Z : Set
\end{code}
\begin{code}
pair-swp' : A × B <-> B × A
pair-swp' = F \ { (a , b) -> (b , a) }
\end{code}

\begin{figure}[t]
\centering
\setlength{\tabcolsep}{0pt}
\begin{tabular}{lclr}
\(x\)   &       &                                                                      &variables\\
\AgdaInductiveConstructor{\(c\)} &       &                                             &\quad Agda constructors\\
\(T\)   &       &                                                                      &Agda terms\\
\(p\)   &\;::=\;&\(x\) \(\mid\)
         \AgdaSymbol{(}\AgdaInductiveConstructor{\(c\)} \([\) \(p\) \(]\)\AgdaSymbol{)}&patterns\\
\(f\)   &\;::=\;&\AgdaFunction{F} \AgdaSymbol{\{} \(bs\) \AgdaSymbol{\}} \(\mid\) \(T\)&flippables\\
\(bs\)  &\;::=\;&\(b\) \(\mid\) \(b\) \AgdaSymbol{;} \(bs\)                            &branches\\
\(b\)   &\;::=\;&\(p\) \(\AgdaSymbol{\ensuremath\leftrightarrow}\) \(B\)               &\\
\(B\)   &\;::=\;&\(p\) \(\mid\) \(p_1\) \AgdaFunction{\ensuremath\langle} \(f\)
               \AgdaFunction{\ensuremath{\rangle}} \(p_2\)
               \AgdaSymbol{\ensuremath{\leftrightarrow}} \(B\)                         &\\
\end{tabular}
\caption{Grammar of the Flipper language. The notation \([\) \(p\)
\(]\) stands for a list of zero or more patterns. Note that
\emph{infix} Agda constructors, such as
\AgdaInductiveConstructor{\AgdaUnderscore{},\AgdaUnderscore{}},
are also allowed in patterns.}
\end{figure}

New flippables can be built from existing ones: the
syntax
\AgdaBound{a}\AgdaSpace{}%
\AgdaFunction{\ensuremath{\langle}}\AgdaSpace{}%
\AgdaBound{f}\AgdaSpace{}%
\AgdaFunction{\ensuremath\rangle}\AgdaSpace{}%
\AgdaBound{b}\AgdaSpace{}%
\AgdaSymbol{\ensuremath{\leftrightarrow}}\AgdaSpace{}%
\AgdaBound{T}\AgdaSpace{}%
is interpreted in \AgdaField{apply} as ``apply the flippable
\(f\) to the variable \(a\) and bind the result to \(b\) in \(T\)'',
equivalent to the expression
\AgdaKeyword{let}\AgdaSpace{}%
\AgdaBound{b}\AgdaSpace{}%
\AgdaSymbol{=}\AgdaSpace{}%
\AgdaField{apply}\AgdaSpace{}%
\AgdaBound{f}\AgdaSpace{}%
\AgdaBound{a}\AgdaSpace{}%
\AgdaKeyword{in}\AgdaSpace{}%
\AgdaBound{T}. We can, for example, compose two flippables as follows:
%replace then "\ensuremath\fatsemi"
%replace \$|  "\ensuremath\langle"
%replace |\$  "\ensuremath\rangle"
\begin{code}
_then_ : (A <-> B) -> (B <-> C) -> A <-> C
f then g = F \  {  a ->  a  $| f  |$ \ { b  -> 
                         b  $| g  |$ \ { c  -> c } } }
\end{code}

To allow for conditional branching, flippable expressions can
contain multiple clauses, corresponding to distinct
input/output patterns. For example, the following flippable swaps the
branches of a sum type:
\begin{code}
sum-swp : Either A B <-> Either B A
sum-swp = F \  {  (left   a)  -> (right  a)
               ;  (right  b)  -> (left   b)
               }
\end{code}
In order for a pattern lambda with multiple clauses to be flippable,
the body expressions on the right hand side must partition the output
type: each possible constructor must appear \emph{exactly once}.

Finally, between being bound and being used, variable names are
considered `in scope', and can be freely referred to inside 
\AgdaFunction{\ensuremath{\langle}}\AgdaSpace{}%
\ensuremath\ldots\AgdaSpace{}%
\AgdaFunction{\ensuremath\rangle}\AgdaSpace{}%
(this doesn't count as a `use'), an example is the way that
\AgdaBound{a} is referred to in the flippable
\AgdaFunction{uncurry} combinator:
%replace Σ "\ensuremath\Sigma"
\begin{code}
uncurry : (A -> B <-> C) -> A × B <-> A × C
uncurry f =
  F \ { (a , b) -> b $| f a |$ \ { c -> (a , c) } }
\end{code}

\section{Bits back coding in Flipper}
As a brief example use case, we show how to implement the `bits-back
with ANS' (BB-ANS) method from \cite{townsend2019} in Flipper. This is
not an implementation of ANS itself, but a method for composing
ANS-based codecs in order to encode data using a latent variable
model.
\begin{figure}[h]
\centering
\begin{tikzpicture}
  \tikzstyle{var}=[circle,draw=black,minimum size=7mm]
  \tikzstyle{latent}  =[]
  \tikzstyle{observed}=[fill=gray!50]
  \node at (0,   0) [var,latent]   (z)  {\(z\)};
  \node at (1.5, 0) [var,observed] (x)  {\(x\)};
  \draw[->]  (z) -- (x);
\end{tikzpicture}
\caption{Graphical model with latent variable \(z\) and observed
variable \(x\).}
\end{figure}

We assume a model over data \(x\) where we only have access to the
joint distribution \(P(x, z)\) for some `latent' variable \(z\), and
an approximate posterior \(Q(z\given x)\), but \emph{not} to the
marginal
\begin{equation}
  P(x) = \int_z P(x, z) \;\mathrm{d}z.
\end{equation}

We define a flippable \AgdaFunction{Encoder} type, parameterized by a compressed
message type, \AgdaBound{C}, and the type \AgdaBound{X} of data to be
compressed:
\begin{code}
Encoder : Set -> Set -> Set
Encoder C X = C × X <-> C
\end{code}
The \AgdaField{apply} function of an \AgdaFunction{Encoder} accepts
some compressed data in \AgdaBound{C} and a symbol in \AgdaBound{X}
and returns a new element of \AgdaBound{C} from which the original
compressed data and the symbol can both be recovered. An
\AgdaFunction{Encoder}
can be
used to compress a list of elements of \AgdaBound{X}, by (flippably)
folding over the list.

The BB-ANS method can be expressed in Flipper as:
%replace prior      "\ensuremath{P_Z}"
%replace likelihood "\ensuremath{P_{X\given Z}}"
%replace posterior  "\ensuremath{Q_{Z\given X}}"
\begin{code}
bb-ans :  (prior       : Encoder C Z)
          (likelihood  : Z -> Encoder C X)
          (posterior   : X -> Encoder C Z)
          -> Encoder C X
bb-ans prior likelihood posterior =
  F \ { (c , x) ->
      c        $| flip (posterior x)  |$ \ { (c , z)  -> 
      (c , x)  $| likelihood z        |$ \ { c        ->
      (c , z)  $| prior               |$ \ { c        -> c } } } }
\end{code}
This matches the Python implementation presented in \cite[Appendix
C]{townsend2019}, but with only one function required instead of two.
\section{Conclusion}
We have presented the Flipper language, for which we have implemented
a compiler as an Agda macro. Flipper can be used to reduce the amount
of code, and to avoid a class of bugs, when implementing lossless
compression programs. We hope to release Flipper, as well as the full
ANS compression implementation in Flipper, as soon as possible.
\newpage
\section*{Acknowledgements}
Thanks to Wouter Swierstra and Heiko Zimmerman for their advice and
feedback on drafts of this paper.
This publication is part of the project ``neural networks for
efficient storage and communication of information'' (with project
number VI.Veni.212.106) of the research programme
``NWO-Talentprogramma Veni ENW 2021'' which is financed by the Dutch
Research Council (NWO).
\printbibliography
\end{document}
