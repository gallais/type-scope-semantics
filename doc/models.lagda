\documentclass[10pt]{sigplanconf}
%insert for 'reprint' option above to get page number+copyright notice
\usepackage{amsmath,amstext,amsthm,amssymb}
\usepackage{agda}
\usepackage{upgreek}
\usepackage{balance}
\usepackage[english]{babel}
\usepackage{hyperref,cleveref}
\usepackage{catchfilebetweentags}

\setlength\mathindent{0em}

\usepackage{mathpartir}

\include{commands}

\newtheorem{lemma}{Lemma}
\newtheorem{theorem}{Theorem}
\newtheorem{corollary}{Corollary}

\begin{document}
\toappear{}
\special{papersize=8.5in,11in}
\setlength{\pdfpageheight}{\paperheight}
\setlength{\pdfpagewidth}{\paperwidth}

%\conferenceinfo{CPP '17}{January 16--17, 2017, Paris, France}
%\copyrightyear{2017}
%\copyrightdata{978-1-4503-4705-1/17/01}
%\proceedings{Proceedings of the 6th ACM SIGPLAN Conference on Certified Programs and Proofs}
%\publicationrights{licensed}
%\copyrightdoi{http://dx.doi.org/10.1145/3018610.3018613}

\title{Type-and-Scope Safe Programs and Their Proofs}
% \subtitle{Subtitle Text, if any}

\authorinfo{Guillaume Allais}
           {gallais@cs.ru.nl}
           {Radboud University, The~Netherlands}
\authorinfo{\hspace*{-0.3in}James Chapman ~ ~ Conor McBride\hspace*{-0.3in}}
           {\hspace*{-0.3in}\{james.chapman,conor.mcbride\}@strath.ac.uk\hspace*{-0.3in}}
           {University of Strathclyde, UK}
\authorinfo{James McKinna}
           {james.mckinna@ed.ac.uk}
           {University of Edinburgh, UK}
\maketitle

\begin{abstract}
We abstract the common type-and-scope safe structure from
computations on $λ$-terms that deliver, e.g., renaming, substitution, evaluation,
CPS-transformation, and printing with a name supply. By
exposing this structure, we can prove generic simulation
and fusion lemmas relating operations built this way.
This work has been fully formalised in Agda.

%We introduce a notion of type and scope preserving semantics
%generalising Goguen and McKinna's ``Candidates for Substitution''
%approach to defining one traversal generic enough to be instantiated
%to renaming first and then substitution. Its careful distinction of
%environment and model values as well as its variation on a structure
%typical of a Kripke semantics make it capable of expressing renaming
%and substitution but also various forms of Normalisation by Evaluation
%and, perhaps more surprisingly, monadic computations such
%as a printing function.

%We then demonstrate that expressing these algorithms in a common
%framework yields immediate benefits: we can deploy some logical
%relations generically over these instances and obtain for instance
%the fusion lemmas for renaming, substitution and normalisation by
%evaluation as simple corollaries of the appropriate fundamental
%lemma. All of this work has been formalised in Agda.

\end{abstract}

\category{D.2.4}{Software / Program Verification}{Correctness Proofs}
\category{D.3.2}{Language Classifications}{Applicative (functional) languages}
\category{F.3.2}{Semantics of Programming Languages}{Denotational semantics, Partial evaluation}

\keywords
Lambda-calculus, Mechanized Meta-Theory, Normalisation by Evaluation, Semantics, Generic Programming, Agda

\section{Introduction}

A programmer implementing an embedded language with bindings has a
wealth of possibilities. However, should she want to be able to inspect
the terms produced by her users in order to optimise or even compile
them, she will have to work with a deep embedding. Which means that she
will have to (re)implement a great number of traversals doing such
mundane things as renaming, substitution, or partial evaluation.
Should she want to get help from the typechecker in order to fend
off common bugs, she can opt for inductive families~\cite{dybjer1991inductive}
to enforce precise invariants. But the traversals now have to be
invariant preserving too!

\begin{figure}[h]
\ExecuteMetaData[motivation.tex]{ren}\vspace{ -1.75em}
\ExecuteMetaData[motivation.tex]{sub}
\caption{Renaming\label{ren} and Substitution\label{sub} for the ST$λ$C}

\ExecuteMetaData[motivation.tex]{kit}
\caption{Kit traversal for the ST$λ$C\label{kit}, for κ of type \AR{Kit} $\blacklozenge{}$}

\ExecuteMetaData[motivation.tex]{nbe}
\caption{Normalisation by Evaluation for the ST$λ$C\label{nbe}}
\end{figure}

In an unpublished manuscript, McBride~(\citeyear{mcbride2005type})
observes the similarity between the types and implementations of
renaming and substitution for simply typed $λ$-calculus (ST$λ$C) in a
dependently typed language as shown in \cref{ren}. There are three
differences between the implemenations of renaming and substitution:
(1) in the variable case, after renaming a variable we must wrap it in
a \AIC{`var} constructor whereas a substitution directly produces a
term; (2) when weakening a renaming to push it under a $λ$ we need
only post-compose the remaning with the De Bruijn variable successor
constructor \AIC{su} (which is essentially weakening for variables)
whereas for a substitution we need a weakening operation for terms
which can be given by renaming via the successor constructor \AF{ren}
\AIC{su}. (3) also in the $λ$ case when pushing a renaming or
substitution under a binder we must extend it to ensure that the
variable bound by the $λ$ mapped to itself. For renaming this involves
extended by the zeroth variable \AIC{ze} whereas for subsitutions we
must extend by the zeroth variable seen as a term \AIC{`var}
\AIC{ze}. He defines a notion of ``Kit'' abstracting these
differences.  The uses of \ARF{Kit.─} operations in the generalising
the traversal function \AF{kit} are shown (in pink) in \cref{kit}.

The contributions of the present paper are twofold:
\begin{itemize}
\item{} We generalise the ``Kit'' approach from syntax to semantics
bringing operations like normalisation (cf.~\cref{nbe}) and printing
with a name supply into our framework.

\item{} We  prove
generic results about simulations between and fusions of semantics
given by, and enabled by, Kit.
\end{itemize}

\paragraph{Outline} We start by defining the simple calculus we will
use as a running example. We then introduce a notion of environments
and one well known instance: the category of renamings. This leads us
to defining a generic notion of type and scope-preserving Semantics
together with a generic evaluation function. We then showcase the
ground covered by these Semantics: from the syntactic ones
corresponding to renaming and substitution to printing with names,
variations of Normalisation by Evaluation or CPS transformations.
Finally, given the generic
definition of Semantics, we can prove fundamental lemmas about these
evaluation functions: we characterise the semantics which can simulate
one another and give an abstract treatment of composition yielding
compaction and reuse of proofs compared to Benton et
al.~(\citeyear{benton2012strongly}).

\paragraph{Notation} This article is a literate Agda file. We hide
telescopes of implicit arguments and \APT{Set} levels, and properly
display (super / sub)-scripts as well as special operators such as
\AF{>>=} or \AF{++}. Colours help: \AIC{green} identifiers are data
constructors, \ARF{pink} names refer to record fields, \AF{blue} is
characteristic of defined symbols, and comments are \AgdaComment{red}
typewrite font. Underscores have a special status: when defining
mixfix identifiers~\cite{danielsson2011parsing}, they mark positions
where arguments may be inserted.

\paragraph{Formalisation} This whole development~\cite{repo}
has been checked by Agda~\cite{norell2009dependently} which guarantees
that all constructions are well typed, and all functions are
total. Nonetheless, it should be noted that the generic model
constructions and the various examples of \AR{Semantics} given here,
although not the proofs, can and have been fully replicated in Haskell
using type families, higher rank polymorphism and GADTs to build
singletons~\cite{eisenberg2013dependently} providing the user with the
runtime descriptions of their types or their contexts' shapes. This
yields, to the best of our knowledge, the first tagless and typeful
implementation of a Kripke-style Normalisation by Evaluation in
Haskell.
\AgdaHide{
\begin{code}
{-# OPTIONS --copatterns #-}
module models where

open import Level as L using (Level ; _⊔_)
open import Data.Empty
open import Data.Unit renaming (tt to ⟨⟩)
open import Data.Bool
open import Data.Sum hiding (map ; [_,_])
open import Data.Product hiding (map)
open import Function as F hiding (_∋_ ; _$_)
\end{code}}

\section{The Calculus and Its Embedding}

\[\begin{array}{rrl}
σ, τ    & ∷= & \mathtt{1} \quad{}|\quad{} \mathtt{2} \quad{}|\quad{} σ → τ \\

b, t, u & ∷= & x \quad{}|\quad{} t\,u \quad{}|\quad{} λx.\, b \quad{}|\quad{}  ⟨⟩ \\
        & |  & \mathtt{tt} \quad{}|\quad{} \mathtt{ff} \quad{}|\quad{} \mathtt{if}~ b ~\mathtt{then}~ t ~\mathtt{else}~ u
\end{array}\]

We work with a deeply embedded simply typed $λ$-calculus.  It
has \texttt{1} and \texttt{2} as base types and serves as a minimal
example of a system with a record type equipped with an η-rule and a
sum type. This grammar is represented in Agda as follows:\vspace*{ -1em}
%We embed each category of the grammar as an inductive family
%in Agda, and to each production corresponds a constructor, which we
%distinguish with a prefix backtick \AIC{`}.
\AgdaHide{
\begin{code}
infixr 20 _`→_
infixl 10 _∙_
\end{code}}
\noindent\begin{tabular}{lr}
\begin{minipage}{0.20\textwidth}
%<*ty>
\begin{code}
data Ty : Set where
  `1 `2  : Ty
  _`→_   : Ty → Ty → Ty
\end{code}
%</ty>
\end{minipage}
&\begin{minipage}{0.20\textwidth}
%<*context>
\begin{code}
data Cx (ty : Set) : Set where
  ε    : Cx ty
  _∙_  : Cx ty → ty → Cx ty
\end{code}
%</context>
\end{minipage}
\end{tabular}
\AgdaHide{
\begin{code}
map^Cx : {ty ty′ : Set} → (ty → ty′) → Cx ty → Cx ty′
map^Cx _ ε        = ε
map^Cx f (Γ ∙ σ)  = map^Cx f Γ ∙ f σ
\end{code}}

To talk about the types of the variables in scope, we need \emph{contexts}.
We choose to represent them as ``snoc'' lists of types; \AIC{ε} denotes the
empty context and \AB{Γ} \AIC{∙} \AB{σ} the context \AB{Γ} extended with a
fresh variable of type \AB{σ}.

To make type signatures more readabale, we introduce combinators acting on
context-indexed types. The most straightforward ones are pointwise lifting
of existing operators on types, and we denote them as dotted versions of
their counterparts: the definition of the pointwise function space \AF{\_⟶\_}
is shown here and the reader will infer the corresponding one for pointwise
disjoint sums (\AF{\_∙⊎\_}) and products (\AF{\_∙×\_}). The ``universally''
operator \AF{[\_]} turn a context-indexed type into a type using an (implicit)
universal quantification. Last but not least, the operator \AF{\_⊢\_} mechanizes
the mathematical convention of only mentioning context \emph{extensions} when
presenting judgements~\cite{martin1982constructive}.\vspace*{ -1em}
\begin{code}
_⟶_ : {ℓ^A ℓ^E : Level} {ty : Set} → (Cx ty → Set ℓ^A) → (Cx ty → Set ℓ^E) → (Cx ty → Set (ℓ^A ⊔ ℓ^E))
(S ⟶ T) Γ = S Γ → T Γ
\end{code}\vspace*{ -2em}
\begin{code}
[_] : {ℓ^A : Level} {ty : Set} → (Cx ty → Set ℓ^A) → Set ℓ^A
[ T ] = ∀ {Γ} → T Γ
\end{code}\vspace*{ -2em}
\begin{code}
_⊢_ : {ℓ^A : Level} {ty : Set} → ty → (Cx ty → Set ℓ^A) → (Cx ty → Set ℓ^A)
(σ ⊢ S) Γ = S (Γ ∙ σ)
\end{code}
\AgdaHide{
\begin{code}
infixr 5 _⟶_
infixr 6 _∙⊎_
_∙⊎_ : {ℓ^A ℓ^E : Level} {ty : Set} → (Cx ty → Set ℓ^A) → (Cx ty → Set ℓ^E) → (Cx ty → Set (ℓ^A ⊔ ℓ^E))
(S ∙⊎ T) Γ = S Γ ⊎ T Γ
infixr 7 _∙×_
_∙×_ : {ℓ^A ℓ^E : Level} {ty : Set} → (Cx ty → Set ℓ^A) → (Cx ty → Set ℓ^E) → (Cx ty → Set (ℓ^A ⊔ ℓ^E))
(S ∙× T) Γ = S Γ × T Γ
infixr 6 _⊢_
\end{code}}
Variables are then positions in such a context represented as typed de
Bruijn~(\citeyear{de1972lambda}) indices. As shown in the comments, this
amounts to an inductive definition of context membership. We use the
combinators defined above to show only local changes to the context.
%<*var>
\begin{code}
data Var {ty : Set} (τ : ty) : Cx ty → Set where
  ze  :            -- ∀ Γ. Var τ (Γ ∙ τ)
                   [          τ ⊢ Var τ ]
  su  :            -- ∀ Γ σ. Var τ Γ → Var τ (Γ ∙ σ)
       {σ : ty} →  [ Var τ ⟶  (σ ⊢ Var τ) ]
\end{code}
%</var>
The syntax for this calculus guarantees that terms are well scoped-and-typed
by construction. This presentation due to
Altenkirch and Reus~(\citeyear{altenkirch1999monadic}) relies heavily on
Dybjer's~(\citeyear{dybjer1991inductive}) inductive families. Rather than
having untyped pre-terms and a typing relation assigning a type to
them, the typing rules are here enforced in the syntax. Notice that
the only use of \AF{\_⊢\_} to extend the context is for the body of
a $λ$.\vspace*{ -1em}
\AgdaHide{
\begin{code}
open import Data.Nat as ℕ using (ℕ ; _+_)

size : {ty : Set} → Cx ty → ℕ
size ε        = 0
size (Γ ∙ _)  = 1 + size Γ

infixl 5 _`$_
\end{code}}
%<*term>
\begin{code}
data Tm : Ty → Cx Ty → Set where
  `var     : {σ : Ty} →    [ Var σ ⟶                 Tm σ         ]
  _`$_     : {σ τ : Ty} →  [ Tm (σ `→ τ) ⟶ Tm σ ⟶    Tm τ         ]
  `λ       : {σ τ : Ty} →  [ σ ⊢ Tm τ ⟶              Tm (σ `→ τ)  ]
  `⟨⟩      :               [                         Tm `1        ]
  `tt `ff  :               [                         Tm `2        ]
  `if      : {σ : Ty} →    [ Tm `2 ⟶ Tm σ ⟶ Tm σ ⟶   Tm σ         ]
\end{code}\vspace*{ -2.5em}
%</term>

\section{A Generic Notion of Environment}

All the semantics we are interested in defining associate to a term \AB{t}
of type \AD{Tm} \AB{σ} \AB{Γ}, a value of type \AB{𝓒} \AB{σ} \AB{Δ} given
an interpretation \AB{𝓔} \AB{Δ} {τ} for each one of its free variables
\AB{τ} in \AB{Γ}. We call the collection of these interpretations an
\AB{𝓔}-(evaluation) environment. We leave out \AB{𝓔} when it can easily
be inferred from the context.
\AgdaHide{
\begin{code}
infix 5 _-Env
\end{code}}
The content of environments may vary wildly between different semantics:
when defining renaming, the environments will carry variables whilst the
ones used for normalisation by evaluation contain elements of the model.
But their structure stays the same which prompts us to define the notion
generically for a notion of \AF{Model}.\vspace*{ -1em}
\begin{code}
Model : {ty : Set} → (ℓ^A : Level) → Set (L.suc ℓ^A)
Model {ty} ℓ^A = ty → Cx ty → Set ℓ^A
\end{code}
Formally, this translates to \AB{𝓔}-environments being the
pointwise lifting of the relation \AB{𝓔} between contexts and types to a
relation between two contexts. Rather than using a datatype to represent
such a lifting, we choose to use a function space. This decision is based
on Jeffrey's observation~(\citeyear{jeffrey2011assoc}) that one can obtain
associativity of append for free by using difference lists. In our case the
interplay between various combinators (e.g. \AF{refl} and \AF{select})
defined later on is vastly simplified by this rather simple decision.\vspace*{ -1em}
%<*environment>
\begin{code}
record _-Env {ℓ^A : Level} {ty : Set} (Γ : Cx ty) (𝓥 : Model ℓ^A) (Δ : Cx ty) : Set ℓ^A
  where  constructor pack
         field lookup : {σ : ty} → Var σ Γ → 𝓥 σ Δ
\end{code}
%</environment>
\AgdaHide{
\begin{code}
open _-Env public

map^Env : {ℓ^A ℓ^B : Level} {ty : Set} {𝓥 : Model ℓ^A} {𝓦 : Model ℓ^B} {Γ Δ Θ : Cx ty}
          (f : {σ : ty} → 𝓥 σ Δ → 𝓦 σ Θ) → (Γ -Env) 𝓥 Δ → (Γ -Env) 𝓦 Θ
lookup (map^Env f ρ) v = f (lookup ρ v)
\end{code}}
Just as an environment interprets variables in a model, a computation
gives a meaning to terms into a model.\vspace*{ -1em}
\begin{code}
_-Comp : {ℓ^A : Level} → Cx Ty → (𝓒 : Model ℓ^A) → Cx Ty → Set ℓ^A
(Γ -Comp) 𝓒 Δ = {σ : Ty} → Tm σ Γ → 𝓒 σ Δ
\end{code}
An appropriate notion of semantics for the calculus is one that
will map environments to computations. In other words, a set of
constraints on $𝓥$ and $𝓒$ guaranteeing the existence of a function
of type: \AF{[} (\AB{Γ} \AR{─Env}) \AB{𝓥} \AF{⟶} (\AB{Γ} \AF{─Comp}) \AB{𝓒} \AF{]}

\AgdaHide{
\begin{code}
infixl 10 _`∙_
\end{code}}
These environments naturally behave like the contexts they are indexed by:
there is a trivial environment for the empty context and one can easily
extend an existing one by providing an appropriate value. The packaging of
the function representing to the environment in a record allows for two
things: it helps the typechecker by stating explicitly which \AF{Model}
the values correspond to and it empowers us to define environments by
copattern-matching~\cite{abel2013copatterns} thus defining environments
by their use cases.\vspace*{ -1em}
\begin{code}
`ε : {ℓ^A : Level} {ty : Set} {𝓥 : Model {ty} ℓ^A} → [ (ε -Env) 𝓥 ]
_`∙_ :  {ℓ^A : Level} {ty : Set} {Γ : Cx ty} {𝓥 : Model ℓ^A} {σ : ty} → [ (Γ -Env) 𝓥 ⟶ 𝓥 σ ⟶ (Γ ∙ σ -Env) 𝓥 ]
\end{code}\vspace*{ -1.75em}
\begin{code}
lookup `ε        ()
lookup (ρ `∙ s)  ze      = s
lookup (ρ `∙ s)  (su n)  = lookup ρ n
\end{code}

\paragraph{The Category of Renamings}\label{category} A key instance
of environments playing a predominant role in this paper is the notion
of renaming. The reader may be accustomed to the more restrictive
notion of renamings as described variously as Order Preserving
Embeddings~\cite{chapman2009type}, thinnings (which we use) or context
inclusions, or just weakenings
~\cite{altenkirch1995categorical}. Writing non-injective or non-order
preserving renamings would take perverse effort given that we only
implement generic interpretations. In practice, although the type of
renamings is more generous, we only introduce weakenings (skipping
variables at the beginning of the context) that become thinnings
(skipping variables at arbitrary points in the context) when we push
them under binders.

A thinning \AB{Γ} \AF{⊆} \AB{Δ} is an environment pairing each variable of
type \AB{σ} in \AB{Γ} to one of the same type in \AB{Δ}.
\AgdaHide{
\begin{code}

infix 5 _⊆_
\end{code}}
\begin{code}
_⊆_ : {ty : Set} (Γ Δ : Cx ty) → Set
Γ ⊆ Δ = (Γ -Env) Var Δ
\end{code}
We formulate a thinning principle using \AF{⊆}. By a ``thinning
principle'', we mean that if \AB{P} holds of \AB{Γ} and \AB{Γ} \AF{⊆}
\AB{Δ} then \AB{P} holds for \AB{Δ} too.  In the case of variables,
thinning merely corresponds to applying the renaming function in
order to obtain a new variable. The environments' case is also quite
simple: being a pointwise lifting of a relation \AB{𝓥} between
contexts and types, they enjoy thinning if \AB{𝓥} does.
\begin{code}
Thinnable : {ty : Set} {ℓ^A : Level} → (Cx ty → Set ℓ^A) → Set ℓ^A
Thinnable {ty} S = {Γ Δ : Cx ty} → Γ ⊆ Δ → (S Γ → S Δ)
\end{code}\vspace*{ -1.5em}
\begin{code}
th^Var : {ty : Set} (σ : ty) → Thinnable (Var σ)
th^Var σ inc v = lookup inc v
\end{code}\vspace*{ -1.5em}
\begin{code}
th[_] :  {ℓ^A : Level} {ty : Set} {𝓥 : Model ℓ^A} → ((σ : ty) → Thinnable (𝓥 σ)) →
         {Γ : Cx ty} → Thinnable ((Γ -Env) 𝓥)
lookup (th[ th ] inc ρ) = th _ inc ∘ lookup ρ
\end{code}
These simple observations allow us to prove that thinnings
form a category which, in turn, lets us provide the user with the
constructors Altenkirch, Hofmann and Streicher's ``Category of
Weakening"~(\citeyear{altenkirch1995categorical}) is based on.
\begin{code}
refl : {ty : Set} {Γ : Cx ty} → Γ ⊆ Γ
refl = pack id
\end{code}\vspace*{ -1.75em}
\begin{code}
select : {ℓ^A : Level} {ty : Set} {Γ Δ Θ : Cx ty} {𝓥 : Model ℓ^A} → Γ ⊆ Δ → (Δ -Env) 𝓥 Θ → (Γ -Env) 𝓥 Θ
lookup (select inc ρ) = lookup ρ ∘ lookup inc
\end{code}\vspace*{ -1.75em}
\begin{code}
step : {ty : Set} {σ : ty} {Γ Δ : Cx ty} → Γ ⊆ Δ → Γ ⊆ (Δ ∙ σ)
step inc = select inc (pack su)
\end{code}\vspace*{ -1.75em}
\begin{code}
pop! : {ty : Set} {σ : ty} {Γ Δ : Cx ty} → Γ ⊆ Δ → (Γ ∙ σ) ⊆ (Δ ∙ σ)
pop! inc = step inc `∙ ze
\end{code}
The modal operator \AF{□} states that a given predicate holds for
all thinnings of a context. It is a closure operator for \AF{Thinnable}.
\begin{code}
□ : {ℓ^A : Level} {ty : Set} → (Cx ty → Set ℓ^A) → (Cx ty → Set ℓ^A)
(□ S) Γ = {Δ : Cx _} → Γ ⊆ Δ → S Δ
\end{code}\vspace*{ -1.75em}
\begin{code}
th^□ : {ℓ^A : Level} {ty : Set} {S : Cx ty → Set ℓ^A} → Thinnable (□ S)
th^□ inc s = s ∘ select inc
\end{code}
Now that we are equipped with the notion of inclusion, we have all
the pieces necessary to describe the Kripke structure of our models
of the simply typed $λ$-calculus.

\section{Semantics and Their Generic Evaluators}

The upcoming sections demonstrate that renaming,
substitution, printing with names, and normalisation by evaluation all
share the same structure. We start by abstracting away a notion of
\AR{Semantics} encompassing all these constructions. This approach
will make it possible for us to implement a generic traversal
parametrised by such a \AR{Semantics} once and for all and to focus
on the interesting model constructions instead of repeating the same
pattern over and over again.

A \AR{Semantics} is indexed by two relations \AB{𝓥} and \AB{𝓒}
describing respectively the values in the environment and the ones
in the model. In cases such as substitution or normalisation by
evaluation, \AB{𝓥} and \AB{𝓒} will happen to coincide but keeping
these two relations distinct is precisely what makes it possible
to go beyond these and also model renaming or printing with names.
The record packs the properties of these relations necessary to
define the evaluation function.\vspace*{ -1em}
\begin{code}
record Semantics {ℓ^E ℓ^M : Level} (𝓥 : Model ℓ^E) (𝓒 : Model ℓ^M) : Set (ℓ^E ⊔ ℓ^M) where
\end{code}
\AgdaHide{
\begin{code}
  infixl 5 _⟦$⟧_
  field
\end{code}}
The first method of a \AR{Semantics} deals with environment values. They
need to be thinnable (\ARF{th}) so that the traversal may introduce fresh
variables when going under a binder whilst keeping the environment well-scoped.\vspace*{ -1em}
\begin{code}
    th      :  (σ : Ty) → Thinnable (𝓥 σ)
\end{code}
The structure of the model is quite constrained: each constructor
in the language needs a semantic counterpart. We start with the
two most interesting cases: \ARF{⟦var⟧} and \ARF{⟦λ⟧}. The variable
case bridges the gap between the fact that the environment translates
variables into values \AB{𝓥} but the evaluation function returns
computations \AB{𝓒}.
\begin{code}
    ⟦var⟧ :  {σ : Ty} → [ 𝓥 σ ⟶ 𝓒 σ ]
\end{code}
The semantic $λ$-abstraction is notable for two reasons: first, following
Mitchell and Moggi~(\citeyear{mitchell1991kripke}), its \AF{□}-structure is
typical of models à la Kripke allowing arbitrary extensions of the context;
and second, instead of being a function in the host language taking
computations to computations,  it takes \emph{values} to computations.
It matches precisely the fact that the body of a $λ$-abstraction exposes
one extra free variable, prompting us to extend the environment with a
value for it. In the special case where \AB{𝓥} = \AB{𝓒} (normalisation
by evaluation for instance), we recover the usual Kripke structure.\vspace*{ -1em}
\AgdaHide{
\begin{code}
  field
\end{code}}
\begin{code}
    ⟦λ⟧ :  {σ τ : Ty} → [ □ (𝓥 σ ⟶ 𝓒 τ) ⟶ 𝓒 (σ `→ τ) ]
\end{code}
The remaining fields' types are a direct translation of the types
of the constructor they correspond to: substructures have simply
been replaced with computations thus making these operators ideal
to combine induction hypotheses.\vspace*{ -1em}
\AgdaHide{
\begin{code}
  field
\end{code}}
\begin{code}
    _⟦$⟧_  : {σ τ : Ty} →  [ 𝓒 (σ `→ τ) ⟶ 𝓒 σ ⟶  𝓒 τ   ]
    ⟦⟨⟩⟧   :               [                     𝓒 `1  ]
    ⟦tt⟧   :               [                     𝓒 `2  ]
    ⟦ff⟧   :               [                     𝓒 `2  ]
    ⟦if⟧   : {σ : Ty} →    [ 𝓒 `2 ⟶ 𝓒 σ ⟶ 𝓒 σ ⟶  𝓒 σ   ]
\end{code}
The type we chose for \ARF{⟦λ⟧} makes the \AF{Semantics} notion
powerful enough that even logical predicates are instances of it. And we
indeed exploit this power when defining normalisation by evaluation
as a semantics: the model construction is, after all, nothing but a logical
predicate. As a consequence it seems rather natural to call \AF{sem}, the
fundamental lemma of semantics. We prove it in a module parameterised by a
\AF{Semantics}, which would correspond to using a Section in Coq. It is
defined by structural recursion on the term. Each constructor is replaced
by its semantic counterpart which combines the induction hypotheses
for its subterms.
\begin{code}
module Eval {ℓ^E ℓ^M : Level} {𝓥 : Model ℓ^E} {𝓒 : Model ℓ^M} (𝓢 : Semantics 𝓥 𝓒) where
 open Semantics 𝓢
\end{code}\vspace*{ -2.5em}%ugly but it works!
%<*evaluation>
\begin{code}
 sem : {Γ : Cx Ty} → [ (Γ -Env) 𝓥 ⟶ (Γ -Comp) 𝓒 ]
 sem ρ (`var v)     = ⟦var⟧ (lookup ρ v)
 sem ρ (t `$ u)     = sem ρ t ⟦$⟧ sem ρ u
 sem ρ (`λ b)       = ⟦λ⟧  (λ σ v →
                           sem (th[ th ] σ ρ `∙ v) b)
 sem ρ `⟨⟩          = ⟦⟨⟩⟧
 sem ρ `tt          = ⟦tt⟧
 sem ρ `ff          = ⟦ff⟧
 sem ρ (`if b l r)  = ⟦if⟧ (sem ρ b) (sem ρ l) (sem ρ r)
\end{code}
%</evaluation>

\section{Syntax Is the Identity Semantics}
\label{syntactic}

As we have explained earlier, this work has been directly influenced by
McBride's ~(\citeyear{mcbride2005type}) manuscript. It seems appropriate
to start our exploration of \AR{Semantics} with the two operations he
implements as a single traversal. We call these operations syntactic
because the computations in the model are actual terms and almost all term
constructors are kept as their own semantic counterpart. As observed by
McBride, it is enough to provide three operations describing the properties
of the values in the environment to get a full-blown \AR{Semantics}. This
fact is witnessed by our simple \AR{Syntactic} record type together with
the \AF{syntactic} function turning its inhabitants into associated
\AR{Semantics}.\vspace*{ -1em}
%<*syntactic>
\begin{code}
record Syntactic {ℓ^A : Level} (𝓥 : Model ℓ^A) : Set ℓ^A where
  field  th     : (σ : Ty) → Thinnable (𝓥 σ)
         var‿0  : {σ : Ty} → [  σ ⊢ 𝓥 σ     ]
         ⟦var⟧  : {σ : Ty} → [  𝓥 σ ⟶ Tm σ  ]
\end{code}\vspace*{ -1.5em}%ugly but it works!
%</syntactic>
\begin{code}
syntactic : {ℓ^A : Level} {𝓥 : Model ℓ^A} → Syntactic 𝓥 → Semantics 𝓥 Tm
syntactic syn = let open Syntactic syn in record
  { th   = th; ⟦var⟧   = ⟦var⟧
  ; ⟦λ⟧  = λ t → `λ (t (step refl) var‿0) ; _⟦$⟧_ = _`$_
  ; ⟦⟨⟩⟧ = `⟨⟩; ⟦tt⟧ = `tt; ⟦ff⟧ = `ff; ⟦if⟧  = `if }
\end{code}
The shape of \ARF{⟦λ⟧} or \ARF{⟦⟨⟩⟧} should not trick the reader
into thinking that this definition performs some sort of η-expansion:
\AF{sem} indeed only ever uses one of these when the evaluated term's
head constructor is already respectively a \AIC{`λ} or a \AIC{`⟨⟩}.
It is therefore absolutely possible to define renaming or substitution
using this approach. We can now port McBride's definitions to our
framework.

\paragraph{Functoriality, also known as Renaming}
Our first example of a \AR{Syntactic} operation works with variables as
environment values. We have already defined thinning earlier (see
Section \ref{category}) and we can turn
a variable into a term by using the \AIC{`var} constructor. The type
of \AF{sem} specialised to this semantics is then precisely the proof
that terms are thinnable.
\AgdaHide{
\begin{code}
syntacticRenaming : Syntactic Var
syntacticRenaming = record { var‿0 = ze; th = th^Var; ⟦var⟧ = `var }

Renaming : Semantics Var Tm; Renaming = syntactic syntacticRenaming
\end{code}}\vspace*{ -1em}
\begin{code}
th^Tm : (σ : Ty) → Thinnable (Tm σ)
th^Tm σ ρ t = let open Eval Renaming in sem ρ t
\end{code}

\paragraph{Simultaneous Substitution}
Our second example of a semantics is another spin on the syntactic model:
environment values are now terms. We get thinning for terms from the
previous example. Again, specialising the type of \AF{sem}
reveals that it delivers precisely the simultaneous substitution.
\AgdaHide{
\begin{code}
syntacticSubstitution : Syntactic Tm
syntacticSubstitution = record { var‿0 = `var ze; th = th^Tm; ⟦var⟧ = id }

Substitution : Semantics Tm Tm; Substitution = syntactic syntacticSubstitution
\end{code}}\vspace*{ -1em}
\begin{code}
subst : {Γ Δ : Cx Ty} {σ : Ty} → (Γ -Env) Tm Δ → Tm σ Γ → Tm σ Δ
subst ρ t = let open Eval Substitution in sem ρ t
\end{code}

\section{Printing with Names}
\label{prettyprint}

Before considering the various model constructions involved in defining
normalisation functions deciding different equational theories, let us
make a detour to a perhaps slightly more surprising example of a
\AF{Semantics}: printing with names. A user-facing project would naturally
avoid directly building a \AD{String} and rather construct an inhabitant of
a more sophisticated datatype in order to generate a prettier output~\cite{hughes1995design,wadler2003prettier}.
But we stick to the simpler setup as \emph{pretty} printing is not our focus here.

This example is interesting for two reasons. Firstly, the distinction between
values and computations is once more instrumental: we get to give the procedure
a precise type guiding our implementation. The environment carries \emph{names}
for the variables currently in scope whilst the computations thread a name-supply
(a stream of strings) to be used to generate fresh names for bound variables.
If the values in the environment had to be computations too, we would not root
out some faulty implementations e.g a program picking a new name each time a
variable is mentioned.\vspace*{ -1em}
\AgdaHide{
\begin{code}
open import Data.Char using (Char)
open import Data.String hiding (show)
open import Data.Nat.Show
open import Data.List as List hiding (_++_ ; zipWith ; [_])
open import Coinduction
open import Data.Stream as Stream using (Stream ; head ; tail ; zipWith ; _∷_)
open import Category.Monad
open import Category.Monad.State
open RawIMonadState (StateMonadState (Stream String)) hiding (zipWith ; pure)
open import Relation.Binary.PropositionalEquality as PEq using (_≡_)
\end{code}
}
\begin{code}
record Name (σ : Ty) (Γ : Cx Ty) : Set where
 constructor mkN; field getN : String
record Printer (σ : Ty) (Γ : Cx Ty) : Set where
  constructor mkP
  field runP : State (Stream String) String
\end{code}
\AgdaHide{
\begin{code}
open Name
open Printer
\end{code}}

Secondly, the fact that the model's computation type is a monad and that this
poses no problem whatsoever in this framework means it is appropriate for
handling languages with effects~\cite{moggi1991notions}, or effectful
semantics e.g. logging the various function calls. Here is the full definition
of the printer assuming the existence of various \AF{format} primitives picking
a way to display \AIC{`λ}, \AIC{`\$} and \AIC{`if}.\vspace*{ -1em}
\AgdaHide{
\begin{code}
formatλ : String → String → String
formatλ x b = "λ" ++ x ++ ". " ++ b

format$ : String → String → String
format$ f t = f ++ " (" ++ t ++ ")"

formatIf : String → String → String → String
formatIf b l r = "if (" ++ b  ++ ") then (" ++ l ++ ") else (" ++ r ++ ")"

domain : ∀ {σ τ Γ} → (□ (Name σ ⟶ Printer τ)) Γ → Ty
domain {σ} _ = σ
\end{code}}
\begin{code}
Printing : Semantics Name Printer
Printing = record
  { th      = λ _ _ → mkN ∘ getN
  ; ⟦var⟧   = mkP ∘ return ∘ getN
  ; _⟦$⟧_   =  λ mf mt → mkP (
               format$ <$> runP mf ⊛ runP mt)
  ; ⟦λ⟧     =  λ mb → mkP (
       get >>= λ ns → let x′ = head ns in
       put (tail ns)                               >>= λ _ →
       runP (mb (step {σ = domain mb} refl) (mkN x′))  >>= λ b′ →
       return (formatλ x′ b′))
  ; ⟦⟨⟩⟧    = mkP (return "⟨⟩")
  ; ⟦tt⟧    = mkP (return "tt")
  ; ⟦ff⟧    = mkP (return "ff")
  ; ⟦if⟧    =  λ mb ml mr → mkP (
       formatIf  <$> runP mb ⊛ runP ml ⊛ runP mr) }
\end{code}

The evaluation function \AF{sem} will deliver a printer which needs to be run
on a \AD{Stream} of distinct \AD{String}s. Our definition of \AF{names} (not
shown here) simply cycles through the letters of the alphabet and guarantess
uniqueness by appending a natural number incremented each time we are back at
the beginning of the cycle. This crude name generation strategy would naturally
be replaced with a more sophisticated one in a user-facing language: we could
e.g. use naming hints for user-introduced binders and type-based schemes otherwise
($f$ or $g$ for function, $i$s or $j$s for integers, etc.).

\AgdaHide{
\begin{code}
flatten : {A : Set} → Stream (A × List A) → Stream A
flatten ((a , as) ∷ aass) = go a as (♭ aass) where
  go : {A : Set} → A → List A → Stream (A × List A) → Stream A
  go a []        aass = a ∷ ♯ flatten aass
  go a (b ∷ as)  aass = a ∷ ♯ go b as aass
names : Stream String
names = flatten (zipWith cons letters ("" ∷ ♯ Stream.map show (allNatsFrom 0)))
  where
    cons : (Char × List Char) → String → (String × List String)
    cons (c , cs) suffix = appendSuffix c , map appendSuffix cs where
      appendSuffix : Char → String
      appendSuffix c  = fromList (c ∷ []) ++ suffix

    letters = Stream.repeat ('a' , toList "bcdefghijklmnopqrstuvwxyz")
    
    allNatsFrom : ℕ → Stream ℕ
    allNatsFrom k = k ∷ ♯ allNatsFrom (1 + k)
\end{code}}

In order to kickstart the evaluation, we still need to provide \AR{Name}s
for each one of the free variables in scope. We deliver that environment
by a simple stateful computation \AF{init} chopping off an initial segment
of the name supply of the appropriate length. The definition of \AF{print}
follows:\vspace*{ -1em}
\AgdaHide{
\begin{code}
nameContext : ∀ Δ Γ → State (Stream String) ((Γ -Env) Name Δ)
nameContext Δ ε        =  return `ε
nameContext Δ (Γ ∙ σ)  =  nameContext Δ Γ >>= λ g →
                          get >>= λ names → put (tail names) >>
                          return (g `∙ mkN (head names))
\end{code}}
\begin{code}
init : {Γ : Cx Ty} → State (Stream String) ((Γ -Env) Name Γ)
\end{code}
\AgdaHide{
\begin{code}
init {Γ} = nameContext Γ Γ
\end{code}}\vspace*{ -2em}%ugly but it works!
\begin{code}
print : {Γ : Cx Ty} {σ : Ty} → Tm σ Γ → String
print {Γ} t = let open Eval Printing in
  proj₁ ((init >>= λ ρ → runP (sem ρ t)) names)
\end{code}
We can observe \AF{print}'s behaviour by writing a test; we state it as a
propositional equality and prove it using \AIC{refl}, forcing the typechecker
to check that both expressions indeed compute to the same normal form. Here
we display the identity function defined in a context of size 2. As we can see,
the binder receives the name \AStr{"c"} because \AStr{"a"} and \AStr{"b"} have
already been assigned to the free variables in scope.\vspace*{ -1em}
\begin{code}
prettyId : {σ : Ty} → print {Γ = ε ∙ `1 ∙ `2} {σ = σ `→ σ} (`λ (`var ze)) ≡ "λc. c"
prettyId = PEq.refl
\end{code}

\section{Normalisation by Evaluation}

Normalisation by Evaluation (NBE) is a technique leveraging the computational
power of a host language in order to normalise expressions of a deeply
embedded one. The process is based on a \AF{Model} construction describing a
family of types by induction on its \AF{Ty} index. Two
procedures are then defined: the first (\AF{eval}) constructs an element
of \AB{𝓒} \AB{σ} \AB{Γ} provided a well typed term of the corresponding
\AD{Tm} \AB{σ} \AB{Γ} type whilst the second (\AF{reify}) extracts, in
a type-directed manner, normal forms \AB{Γ} \AD{⊢^{nf}} \AB{σ} from elements
of the model \AB{𝓒} \AB{σ} \AB{Γ}. NBE composes the two procedures. The
definition of this \AF{eval} function is a natural candidate for our
\AF{Semantics} framework. NBE is always defined \emph{for} a
given equational theory; we start by recalling the various
rules a theory may satisfy.

Thanks to \AF{Renaming} and \AF{Substitution} respectively, we can formally
define η-expansion and β-reduction. The η-rules say that for some types,
terms have a canonical form: functions will all be λ-headed whilst records will
collect their fields --- here this makes all elements of
\AIC{`1} equal to \AIC{`⟨⟩}.\vspace*{ -1em}
\AgdaHide{
\begin{code}
infixl 10 _⟨_/var₀⟩
\end{code}}
\begin{code}
eta : {σ τ : Ty} → [ Tm (σ `→ τ) ⟶ Tm (σ `→ τ) ]
eta t = `λ (th^Tm _ (step refl) t `$ `var ze)
\end{code}\vspace*{ -1.75em}
\begin{code}
_⟨_/var₀⟩ : {σ τ : Ty} → [ σ ⊢ Tm τ ⟶ Tm σ ⟶ Tm τ ] 
t ⟨ u /var₀⟩ = subst (pack `var `∙ u) t
\end{code}\vspace*{ -1.5em}
\begin{mathpar}
\inferrule{\text{\AB{t} \AS{:} \AD{Tm} (\AB{σ} \AIC{`→} \AB{τ}) \AB{Γ}}
  }{\text{\AB{t} ↝ \AF{eta} \AB{t}}
  }{η_1}
\and \inferrule{\text{\AB{t} \AS{:} \AD{Tm} \AIC{`1} \AB{Γ}}
  }{\text{\AB{t} ↝ \AIC{`⟨⟩}}
  }{η_2}
\end{mathpar}\vspace*{ -1em}
\begin{mathpar}
\inferrule{
  }{\text{(\AIC{`λ} \AB{t}) \AIC{`\$} \AB{u} ↝ \AB{t} \AF{⟨} \AB{u} \AF{/var₀⟩}}
  }{β}
\end{mathpar}
The β-rule is the main driver for actual computation,
but the presence of an inductive data type (\AIC{`2}) and its eliminator
(\AIC{`if}) means we have further redexes: whenever the
boolean the eliminator branches on is in canonical form, we may apply
a ι-rule. Finally, the ξ-rule lets us reduce under
$λ$-abstractions --- the distinction between weak-head normalisation and
strong normalisation.\vspace*{ -1.5em}
\begin{mathpar}
\inferrule{
  }{\text{\AIC{`if} \AIC{`tt} \AB{l} \AB{r} ↝ \AB{l}}
  }{ι_1}
\and
\inferrule{
  }{\text{\AIC{`if} \AIC{`ff} \AB{l} \AB{r} ↝ \AB{r}}
  }{ι_2}
\and
\inferrule{\text{\AB{t} ↝ \AB{u}}
  }{\text{\AIC{`λ} \AB{t} ↝ \AIC{`λ} \AB{u}}
  }{ξ}
\end{mathpar}

Now that we have recalled all these rules, we can talk precisely about the
sort of equational theory decided by the model construction we choose to
perform. We start with the usual definition of NBE
which goes under λs and produces η-long βι-short normal forms.

\subsection{Normalisation by Evaluation for βιξη}
\label{normbye}

In the case of NBE, the environment values
and the computations in the model will both have the same type \AF{Kr}
(standing for ``Kripke''), defined by induction on the \AD{Ty} argument.
The η-rules allow us to represent functions (resp. inhabitants
of \AIC{`1}) in the source language as function spaces (resp. \AR{⊤}).
In Agda, there are no such rules for boolean values. We thus need
a notion of syntactic normal forms.
We parametrise the mutually defined inductive families \AD{Ne} and \AD{Nf}
by a predicate \AB{R} constraining the types at which one may embed a neutral
as a normal form. This make it possible to control the way
NBE $η$-expands all terms at certain types.
\AgdaHide{
\begin{code}
module NormalForms (R : Ty → Set) where

 mutual
\end{code}}\vspace*{ -1em}
\begin{code}
  data Ne : Model L.zero  where
    `var   : {σ : Ty} →    [ Var σ ⟶                Ne σ ]
    _`$_   : {σ τ : Ty} →  [ Ne (σ `→ τ) ⟶ Nf σ ⟶   Ne τ ]
    `if  : {σ : Ty} →      [ Ne `2 ⟶ Nf σ ⟶ Nf σ ⟶  Ne σ ]
\end{code}\vspace*{ -1.75em}
\begin{code}
  data Nf : Model L.zero where
    `ne      : {σ : Ty} → R σ →   [ Ne σ ⟶      Nf σ         ]
    `⟨⟩      :                    [             Nf `1        ]
    `tt `ff  :                    [             Nf `2        ]
    `λ       : {σ τ : Ty} →       [ σ ⊢ Nf τ ⟶  Nf (σ `→ τ)  ]
\end{code}
Once more, the expected notions of thinning \AF{th^ne} and \AF{th^nf}
are induced as \AD{Nf} and \AD{Ne} are syntaxes. We omit their purely
structural implementation here and wish we could do so in source code,
too: our constructions so far have been syntax-directed and could
surely be leveraged by a generic account of syntaxes with binding.
\AgdaHide{
\begin{code}
 th^ne : (σ : Ty) → Thinnable (Ne σ)
 th^nf : (σ : Ty) → Thinnable (Nf σ)

 th^ne σ inc (`var v)        = `var (th^Var σ inc v)
 th^ne σ inc (ne `$ u)       = th^ne _ inc ne `$ th^nf _ inc u
 th^ne σ inc (`if ne l r)  = `if (th^ne `2 inc ne) (th^nf σ inc l) (th^nf σ inc r)

 th^nf σ         inc (`ne pr t) = `ne pr (th^ne σ inc t)
 th^nf `1     inc `⟨⟩           = `⟨⟩
 th^nf `2     inc `tt           = `tt
 th^nf `2     inc `ff           = `ff
 th^nf (σ `→ τ)  inc (`λ nf)       = `λ (th^nf τ (pop! inc) nf)

 infix 5 [_,,_]
 [_,,_] : {ℓ^A : Level} {Γ : Cx Ty} {τ : Ty} {P : (σ : Ty) (pr : Var σ (Γ ∙ τ)) → Set ℓ^A} →
         (p0 : P τ ze) →
         (pS : (σ : Ty) (n : Var σ Γ) → P σ (su n)) →
         (σ : Ty) (pr : Var σ (Γ ∙ τ)) → P σ pr
 [ p0 ,, pS ] σ ze    = p0
 [ p0 ,, pS ] σ (su n)  = pS σ n

 mutual

  th^nf-refl′ : {Γ : Cx Ty} {σ : Ty} {f : Γ ⊆ Γ}
                (prf : (σ : Ty) (pr : Var σ Γ) → lookup f pr ≡ pr) →
                (t : Nf σ Γ) → th^nf σ f t ≡ t
  th^nf-refl′ prf (`ne pr t)  = PEq.cong (`ne pr) (th^ne-refl′ prf t)
  th^nf-refl′ prf `⟨⟩            = PEq.refl
  th^nf-refl′ prf `tt            = PEq.refl
  th^nf-refl′ prf `ff            = PEq.refl
  th^nf-refl′ prf (`λ t)         = PEq.cong `λ (th^nf-refl′ ([ PEq.refl ,, (λ σ → PEq.cong su ∘ prf σ) ]) t)

  th^ne-refl′ : {Γ : Cx Ty} {σ : Ty} {f : Γ ⊆ Γ}
                (prf : (σ : Ty) (pr : Var σ Γ) → lookup f pr ≡ pr) →
                (t : Ne σ Γ) → th^ne σ f t ≡ t
  th^ne-refl′ prf (`var v)       = PEq.cong `var (prf _ v)
  th^ne-refl′ prf (t `$ u)       = PEq.cong₂ _`$_ (th^ne-refl′ prf t) (th^nf-refl′ prf u)
  th^ne-refl′ prf (`if b l r)  = PEq.cong₂ (uncurry `if) (PEq.cong₂ _,_ (th^ne-refl′ prf b) (th^nf-refl′ prf l)) (th^nf-refl′ prf r)

 mutual

  th^nf-trans′ : {Θ Δ Γ : Cx Ty} {σ : Ty} {inc₁ : Γ ⊆ Δ} {inc₂ : Δ ⊆ Θ}
                 {f : Γ ⊆ Θ} (prf : (σ : Ty) (pr : Var σ Γ) → lookup (select inc₁ inc₂) pr ≡ lookup f pr)
                 (t : Nf σ Γ) →  th^nf σ inc₂ (th^nf σ inc₁ t) ≡ th^nf σ f t
  th^nf-trans′ prf (`ne pr t)  = PEq.cong (`ne pr) (th^ne-trans′ prf t)
  th^nf-trans′ prf `⟨⟩            = PEq.refl 
  th^nf-trans′ prf `tt            = PEq.refl
  th^nf-trans′ prf `ff            = PEq.refl
  th^nf-trans′ prf (`λ t)         = PEq.cong `λ (th^nf-trans′ ([ PEq.refl ,, (λ σ → PEq.cong su ∘ prf σ) ]) t)

  th^ne-trans′ : {Θ Δ Γ : Cx Ty} {σ : Ty} {inc₁ : Γ ⊆ Δ} {inc₂ : Δ ⊆ Θ}
                 {f : Γ ⊆ Θ} (prf : (σ : Ty) (pr : Var σ Γ) → lookup (select inc₁ inc₂) pr ≡ lookup f pr)
                 (t : Ne σ Γ) →  th^ne σ inc₂ (th^ne σ inc₁ t) ≡ th^ne σ f t
  th^ne-trans′ prf (`var v)       = PEq.cong `var (prf _ v)
  th^ne-trans′ prf (t `$ u)       = PEq.cong₂ _`$_ (th^ne-trans′ prf t) (th^nf-trans′ prf u)
  th^ne-trans′ prf (`if b l r)  = PEq.cong₂ (uncurry `if) (PEq.cong₂ _,_ (th^ne-trans′ prf b) (th^nf-trans′ prf l)) (th^nf-trans′ prf r)

 th^nf-refl : {Γ : Cx Ty} {σ : Ty} (t : Nf σ Γ) → th^nf σ refl t ≡ t
 th^nf-refl = th^nf-refl′ (λ _ _ → PEq.refl)

 th^ne-refl : {Γ : Cx Ty} {σ : Ty} (t : Ne σ Γ) → th^ne σ refl t ≡ t
 th^ne-refl = th^ne-refl′ (λ _ _ → PEq.refl)

 th^nf-trans : {Θ Δ Γ : Cx Ty} {σ : Ty} (inc₁ : Γ ⊆ Δ) (inc₂ : Δ ⊆ Θ)
              (t : Nf σ Γ) →  th^nf σ inc₂ (th^nf σ inc₁ t) ≡ th^nf σ (select inc₁ inc₂) t
 th^nf-trans inc₁ inc₂ = th^nf-trans′ (λ _ _ → PEq.refl)

 th^ne-trans : {Θ Δ Γ : Cx Ty} {σ : Ty} (inc₁ : Γ ⊆ Δ) (inc₂ : Δ ⊆ Θ)
              (t : Ne σ Γ) →  th^ne σ inc₂ (th^ne σ inc₁ t) ≡ th^ne σ (select inc₁ inc₂) t
 th^ne-trans inc₁ inc₂ = th^ne-trans′ (λ _ _ → PEq.refl)
\end{code}}
We now define the model. The \AR{R} predicate
characterising the types for which neutral terms may be considered
normal is here equivalent to the unit type for \AIC{`2} and the
empty type otherwise. This makes us use η-rules
eagerly: all inhabitants of \AD{Nf} \AB{Γ} \AIC{`1} and
\AD{Nf} \AB{Γ} (\AB{σ} \AIC{`→} \AB{τ}) are equal to \AIC{`⟨⟩} and
\AIC{`λ}-headed respectively.

The model construction then follows the usual pattern pioneered by
Berger~(\citeyear{berger1993program}) and formally analysed and thoroughly
explained by Catarina Coquand~(\citeyear{coquand2002formalised}). We work
by induction on the type and describe η-expanded values: all inhabitants
of \AF{Kr} \AIC{`1} \AB{Γ} are equal and all elements
of \AF{Kr} (\AB{σ} \AIC{`→} \AB{τ}) \AB{Γ} are functions in Agda.
\AgdaHide{
\begin{code}
module βιξη where
 R : Ty → Set
 R `2 = ⊤
 R _ = ⊥
 open NormalForms R public
\end{code}}
%<*sem>
\begin{code}
 Kr : Model _
 Kr `1     = const ⊤
 Kr `2     = Nf `2
 Kr (σ `→ τ)  = □ (Kr σ ⟶ Kr τ)
\end{code}
%</sem>
This model is defined by induction on the type in terms either of
syntactic objects (\AD{Nf}) or using the \AF{□}-operator which is
a closure operator for Thinnings. As such, it is trivial to prove
that for all type \AB{σ}, \AF{Kr} \AB{σ} is \AF{Thinnable}.
\AgdaHide{
\begin{code}
 th^Kr : (σ : Ty) → Thinnable (Kr σ)
 th^Kr `1        = const id
 th^Kr `2        = th^nf `2
 th^Kr (σ `→ τ)  = th^□
\end{code}}
Application's semantic counterpart is easy to define: given that \AB{𝓥}
and \AB{𝓒} are equal in this instance definition, we just feed the argument
directly to the function, with the identity renaming: \AB{f} \AF{\$\$} \AB{t} \AS{=} \AB{f} \AF{refl} \AB{t}.
\AgdaHide{
\begin{code}
 infixr 5 _$$_

 _$$_ : {σ τ : Ty} → [ Kr (σ `→ τ) ⟶ Kr σ ⟶ Kr τ ]
 t $$ u = t refl u
\end{code}}
Conditional branching however is more subtle: the boolean value \AIC{`if} branches on
may be a neutral term in which case the whole elimination form
is stuck. This forces us to define \AF{reify} and \AF{reflect} first. These
functions, also known as quote and unquote respectively, give the interplay
between neutral terms, model values and normal forms. \AF{reflect} performs a
form of semantic η-expansion: all stuck \AIC{`1} terms are equated and all functions
are $λ$-headed. It allows us to define \AF{var‿0}, the semantic counterpart of \AIC{`var} \AIC{ze}.\vspace*{ -1em}
\AgdaHide{
\begin{code}
 var‿0 : (σ : Ty) → [ σ ⊢ Kr σ ]
\end{code}}
\begin{code}
 reify    : (σ : Ty) → [ Kr σ ⟶ Nf σ ]
 reflect  : (σ : Ty) → [ Ne σ ⟶ Kr σ ]
\end{code}\vspace*{ -1em}
\AgdaHide{
\begin{code}
 var‿0 σ = reflect σ (`var ze)
\end{code}}\vspace*{ -1em}
\begin{code}
 reflect `1        t = ⟨⟩
 reflect `2        t = `ne _ t
 reflect (σ `→ τ)  t =  λ ρ u → let b = th^ne (σ `→ τ) ρ t 
                        in reflect τ (b `$ reify σ u)
\end{code}\vspace*{ -2em}
\begin{code}
 reify `1        T = `⟨⟩
 reify `2        T = T
 reify (σ `→ τ)  T = `λ (reify τ (T (step refl) (var‿0 σ)))
\end{code}

We can then give the semantics of \AIC{`if}: if the boolean
is a value, the appropriate branch is picked; if it is stuck the whole expression
is reflected in the model.
\begin{code}
 if : {σ : Ty} → [ Kr `2 ⟶ Kr σ ⟶ Kr σ ⟶ Kr σ ]
 if `tt            l r = l
 if `ff            l r = r
 if {σ} (`ne _ T)  l r = reflect σ (`if T (reify σ l) (reify σ r))
\end{code}
We can then combine these components. The semantics of
a $λ$-abstraction is simply the identity function: the structure of the
functional case in the definition of the model matches precisely the shape
expected in a \AF{Semantics}. Because the environment carries model values,
the variable case is trivial. We obtain a normaliser by kickstarting the
evaluation with a dummy environment of reflected variables.\vspace*{ -1em}
\begin{code}
 Normalise : Semantics Kr Kr
 Normalise = record
   { th = th^Kr; ⟦var⟧ = id; _⟦$⟧_ = λ {σ} {τ} → _$$_ {σ} {τ}; ⟦λ⟧ = id
   ; ⟦⟨⟩⟧ = ⟨⟩; ⟦tt⟧ = `tt; ⟦ff⟧ = `ff; ⟦if⟧ = λ {σ} → if {σ} }
\end{code}\vspace*{ -1.75em}
\begin{code}
 nbe : {Γ : Cx Ty} → [ (Γ -Env) Kr ⟶ (Γ -Comp) Kr ]
 nbe ρ t = let open Eval Normalise in sem ρ t
\end{code}\vspace*{ -1.75em}
\begin{code}
 norm : (σ : Ty) → [ Tm σ ⟶ Nf σ ]
 norm σ t = reify σ (nbe (pack (reflect _ ∘ `var)) t)
\end{code}\vspace*{ -1.5em}

\subsection{Normalisation by Evaluation for βιξ}

As seen above, the traditional typed model construction leads to an NBE
procedure outputting βι-normal η-long terms. However actual proof systems
rely on evaluation strategies that avoid applying η-rules
as much as possible: unsurprisingly, it is a rather bad idea to η-expand proof
terms which are already large when typechecking complex developments.
%Garillot\todo{not true, fix up: normalise and compare\cite{coquand1991algorithm}}
%and colleagues~\cite{garillot2009packaging} report that common mathematical
%structures packaged in records can lead to terms of such a size that theorem
%proving becomes impractical.

In these systems, normal forms are neither η-long nor η-short: the η-rule is
never deployed except when comparing a neutral and a constructor-headed term
for equality. Instead of declaring
them distinct, the algorithm does one step of η-expansion on the
neutral term and compares their subterms structurally. The conversion test
fails only when confronted with neutral terms with distinct head
variables or normal forms with different head constructors.

To reproduce this behaviour, NBE must be amended.
It is possible to alter the model definition described earlier so that it
avoids unnecessary η-expansions. We proceed by enriching the traditional
model with extra syntactical artefacts in a manner reminiscent of Coquand
and Dybjer's~(\citeyear{CoqDybSK}) approach to defining an NBE procedure for the SK combinator calculus. Their resorting to glueing
terms to elements of the model was dictated by the sheer impossibily to write
a sensible reification procedure but, in hindsight, it provides us with a
powerful technique to build models internalizing alternative equational
theories.

This leads us to using a predicate \AF{R} allowing embedding of neutrals
into normal forms at all types and mutually defining the model (\AF{Kr})
together with the \emph{acting} model (\AF{Go}):\vspace*{ -1em}
\AgdaHide{
\begin{code}
module βιξ where

 R : Ty → Set
 R = const ⊤
  
 open NormalForms R public

 mutual
\end{code}}
\noindent\begin{tabular}{l@{\hskip 2em}r}
\hspace{-0.5cm}\begin{minipage}[t]{0.15\textwidth}
\begin{code}
  Kr : Model _
  Kr σ = Ne σ ∙⊎ Go σ
\end{code}
\end{minipage}
&\begin{minipage}[t]{0.25\textwidth}
\begin{code}
  Go : Model _
  Go `1        = const ⊤
  Go `2        = const Bool
  Go (σ `→ τ)  = □ (Kr σ ⟶ Kr τ)
\end{code}
\end{minipage}
\end{tabular}

% These mutual definitions allow us to make a careful distinction between values
% arising from (non expanded) stuck terms and the ones wich are constructor headed
% and have a computational behaviour associated to them. The values in the acting
% model are storing these behaviours be it either actual proofs of \AF{⊤}, actual
% \AF{2}eans or actual Agda functions depending on the type of the term. It is
% important to note that the functions in the acting model have the model as both
% domain and codomain: there is no reason to exclude the fact that both the argument
% or the body may or may not be stuck.

% (σ : Ty) → Thinnable for these structures is rather straightforward
% albeit slightly more complex than for the usual definition of Normalisation
% by Evaluation seen in Section ~\ref{normbye}.
\AgdaHide{
\begin{code}
  th^Go : (σ : Ty) → Thinnable (Go σ)
  th^Go `1        = const id
  th^Go `2        = const id
  th^Go (σ `→ τ)  = th^□

  th^Kr : (σ : Ty) → Thinnable (Kr σ)
  th^Kr σ inc (inj₁ ne)  = inj₁ (th^ne σ inc ne)
  th^Kr σ inc (inj₂ T)   = inj₂ (th^Go σ inc T)
\end{code}}

% What used to be called reflection in the previous model is now trivial:
% stuck terms are indeed perfectly valid model values. Reification becomes
% quite straightforward too because no η-expansion is needed. When facing
% a stuck term, we simply embed it in the set of normal forms. Even though
% \AF{reify^{βιξ⋆}} may look like it is performing some η-expansions, it
% is not the case: all the values in the acting model are notionally obtained
% from constructor-headed terms.
\AgdaHide{
\begin{code}
  reflect : (σ : Ty) → [ Ne σ ⟶ Kr σ ]
  reflect σ = inj₁

  reify   : (σ : Ty) → [ Kr σ ⟶ Nf σ ]
  reify⋆  : (σ : Ty) → [ Go σ ⟶ Nf σ ]

  reify σ (inj₁ ne)  = `ne _ ne
  reify σ (inj₂ T)   = reify⋆ σ T

  reify⋆ `1     T = `⟨⟩
  reify⋆ `2     T = if T then `tt else `ff
  reify⋆ (σ `→ τ)  T = `λ (reify τ (T (step refl) var‿0))
    where var‿0 = inj₁ (`var ze)
\end{code}}
Most combinators acting on this model follow a pattern similar to their
counterpart's in the previous section. Semantic application is
more interesting: in case the function is a stuck term, we grow its
spine by reifying its argument; otherwise we have an Agda function ready
to be applied. We proceed similarly for the definition of the semantical
``if'' (omitted here). Altogether, we get another
normaliser which is, this time, \emph{not} producing η-long normal forms.\vspace*{ -1em}
\begin{code}
  _$$_ : {σ τ : Ty} → [ Kr (σ `→ τ) ⟶ Kr σ ⟶ Kr τ ]
  (inj₁ ne)  $$ u = inj₁ (ne `$ reify _ u)
  (inj₂ F)   $$ u = F refl u
\end{code}
\AgdaHide{
\begin{code}
  if : {σ : Ty} → [ Kr `2 ⟶ Kr σ ⟶ Kr σ ⟶ Kr σ ]
  if (inj₁ ne) l r = inj₁ (`if ne (reify _ l) (reify _ r))
  if (inj₂ T)  l r = if T then l else r
\end{code}}
% Finally, we have all the necessary components to show that evaluating
% the term whilst not η-expanding all stuck terms is a perfectly valid
% \AR{Semantics}. As usual, normalisation is defined by composing
% reification and evaluation on the diagonal environment.
\AgdaHide{
\begin{code}
  Normalise : Semantics Kr Kr
  Normalise = record
    { th = th^Kr; ⟦var⟧   = id
    ; _⟦$⟧_ = _$$_; ⟦λ⟧ = inj₂
    ; ⟦⟨⟩⟧ = inj₂ ⟨⟩; ⟦tt⟧ = inj₂ true; ⟦ff⟧ = inj₂ false; ⟦if⟧  = if }

  norm : (σ : Ty) → [ Tm σ ⟶ Nf σ ]
  norm σ t = let open Eval Normalise in reify σ (sem (pack (reflect _ ∘ `var)) t)
\end{code}}

\subsection{Normalisation by Evaluation for βι}

The decision to apply the η-rule lazily can be pushed even further: one may
forgo using the ξ-rule too and simply perform weak-head normalisation. This
drives computation only when absolutely necessary, e.g.
when two terms compared for equality have matching head constructors
and one needs to inspect these constructors' arguments to conclude.

% For
% that purpose, we introduce an inductive family describing terms in weak-head
% normal forms. Naturally, it is possible to define the corresponding thinnings
% \AF{th^{whne}} and \AF{th^{whnf}} as well as erasure functions \AF{erase^{whnf}}
% and \AF{erase^{whne}} with codomain \AD{\_⊢\_} (we omit their simple definitions here).
\AgdaHide{
\begin{code}
module βι where

 data Whne : Model L.zero where
   `var   : {σ : Ty} → [ Var σ ⟶ Whne σ ]
   _`$_   : {σ τ : Ty} → [ Whne (σ `→ τ) ⟶ Tm σ ⟶ Whne τ ]
   `if  : {σ : Ty} → [ Whne `2 ⟶ Tm σ ⟶ Tm σ ⟶ Whne σ ]

 data Whnf : Model L.zero where
  `ne   : {σ : Ty} → [ Whne σ ⟶ Whnf σ ]
  `⟨⟩      : [ Whnf `1 ]
  `tt `ff  : [ Whnf `2 ]
  `λ       : {σ τ : Ty} → [ σ ⊢ Tm τ ⟶ Whnf (σ `→ τ) ]
\end{code}}
\AgdaHide{
\begin{code}
 th^whne : (σ : Ty) → Thinnable (Whne σ)
 th^whnf : (σ : Ty) → Thinnable (Whnf σ)
 th^whne σ inc (`var v)        = `var (th^Var σ inc v)
 th^whne σ inc (ne `$ u)       = th^whne _ inc ne `$ th^Tm _ inc u
 th^whne σ inc (`if ne l r)  = `if (th^whne `2 inc ne) (th^Tm σ inc l) (th^Tm σ inc r)

 th^whnf σ         inc (`ne t)  = `ne (th^whne σ inc t)
 th^whnf `1     inc `⟨⟩         = `⟨⟩
 th^whnf `2     inc `tt         = `tt
 th^whnf `2     inc `ff         = `ff
 th^whnf (σ `→ τ)  inc (`λ b)      = `λ (th^Tm τ (pop! inc) b)

 erase^whne : {σ : Ty} → [ Whne σ ⟶ Tm σ ]
 erase^whne (`var v)       = `var v
 erase^whne (t `$ u)       = erase^whne t `$ u
 erase^whne (`if t l r)  = `if (erase^whne t) l r
\end{code}}

The model construction is much like the previous one except
that source terms are now stored in the model too. This means that
from an element of the model, one can pick either the reduced version
of the input term (i.e. a stuck term or the term's computational
content) or the original. We exploit this ability most
notably in reification where once we have obtained either a
head constructor or a head variable, no subterms need
be evaluated.\vspace*{ -1em}

\AgdaHide{
\begin{code}
 mutual
\end{code}}
\noindent\begin{tabular}{l@{\hskip 2em}r}
\hspace{-0.5cm}\begin{minipage}[t]{0.15\textwidth}
\begin{code}
  Kr : Model _
  Kr σ  = Tm σ ∙×
    (Whne σ ∙⊎ Go σ)
\end{code}
\end{minipage}
&\begin{minipage}[t]{0.25\textwidth}
\begin{code}
  Go : Model _
  Go `1        = const ⊤
  Go `2        = const Bool
  Go (σ `→ τ)  = □ (Kr σ ⟶ Kr τ)
\end{code}
\end{minipage}
\end{tabular}

\AgdaHide{
\begin{code}
 th^Go : (σ : Ty) → Thinnable (Go σ)
 th^Go `1        inc T = T
 th^Go `2        inc T = T
 th^Go (σ `→ τ)  inc T = λ inc′ → T (select inc inc′)

 th^Kr : (σ : Ty) → Thinnable (Kr σ)
 th^Kr σ inc (t , inj₁ ne)  = th^Tm σ inc t , inj₁ (th^whne σ inc ne)
 th^Kr σ inc (t , inj₂ T)   = th^Tm σ inc t , inj₂ (th^Go σ inc T)

 reflect : (σ : Ty) → [ Whne σ ⟶ Kr σ ]
 reflect σ t = erase^whne t , inj₁ t

 var‿0 : {σ : Ty} → [ σ ⊢ Kr σ ]
 var‿0 = reflect _ (`var ze)

 mutual

  reify⋆ : (σ : Ty) → [ Go σ ⟶ Whnf σ ]
  reify⋆ `1     T = `⟨⟩
  reify⋆ `2     T = if T then `tt else `ff
  reify⋆ (σ `→ τ)  T = `λ (proj₁ (T (step refl) var‿0))

  reify : (σ : Ty) → [ Kr σ ⟶ Whnf σ ]
  reify σ (t , inj₁ ne) = `ne ne
  reify σ (t , inj₂ T)  = reify⋆ σ T
\end{code}}

% (σ : Ty) → Thinnable, reflection, and reification can all be defined rather
% straightforwardly based on the template provided by the previous
% section. The application and conditional branching rules are more
% interesting: one important difference with respect to the previous
% subsection is that we do not grow the spine of a stuck term using
% reified versions of its arguments but rather the corresponding
% \emph{source} term thus staying true to the idea that we only head
% reduce enough to expose either a constructor or a variable.

\AgdaHide{
\begin{code}
 _$$_ :  {σ τ : Ty} → [ Kr (σ `→ τ) ⟶ Kr σ ⟶ Kr τ ]
 (t , inj₁ ne)  $$ (u , U) = t `$ u , inj₁ (ne `$ u)
 (t , inj₂ T)   $$ (u , U) = t `$ u , proj₂ (T refl (u , U))

 if : {σ : Ty} → [ Kr `2 ⟶ Kr σ ⟶ Kr σ ⟶ Kr σ ]
 if (b , inj₁ ne)  (l , L) (r , R) = `if b l r , inj₁ (`if ne l r)
 if (b , inj₂ B)   (l , L) (r , R) = `if b l r , (if B then L else R)
\end{code}}

% We can finally put together all of these semantic counterpart to
% obtain a \AR{Semantics} corresponding to weak-head normalisation.
% We omit the now self-evident definition of \AF{norm^{βι}} as the
% composition of evaluation and reification.

\AgdaHide{
\begin{code}
 Normalise : Semantics Kr Kr
 Normalise = record
   { th = th^Kr; ⟦var⟧ = id
   ; _⟦$⟧_ = _$$_; ⟦λ⟧ = λ t → `λ (proj₁ (t (step refl) (reflect _ (`var ze)))) , inj₂ t
  ; ⟦⟨⟩⟧ = `⟨⟩ , inj₂ ⟨⟩; ⟦tt⟧ = `tt  , inj₂ true; ⟦ff⟧ = `ff  , inj₂ false; ⟦if⟧  = if }

 whnorm : (σ : Ty) → [ Tm σ ⟶ Whnf σ ]
 whnorm σ t = let open Eval Normalise in reify σ (sem (pack (reflect _ ∘ `var)) t)
\end{code}}

\section{CPS Transformation}
\label{cps-transformation}

In their generic account of continuation passing styles, Hatcliff and
Danvy~(\citeyear{hatcliff1994generic}) decompose both call by name and
call by value CPS transformations in two phases. The first one, an
embedding of the source language into Moggi's Meta Language~(\citeyear{moggi1991notions}),
picks an evaluation strategy whilst the second one is a generic erasure
from Moggi's ML back to the original language. Looking closely at the
structure of the first pass, we can see that it is an instance of our
Semantics framework. Let us start with the definition of Moggi's Meta
Language. Its types are fairly straightforward, we simply have an extra
constructor \AIC{\#\_} for computations and the arrow has been turned
into a \emph{computational} arrow meaning that its codomain is considered
to be a computational type:\vspace*{-1.5em}
\AgdaHide{
\begin{code}
infixr 20 #_
infixr 15 _`→#_
\end{code}}
\begin{code}
data CTy : Set where
  `1 `2   : CTy
  _`→#_   : CTy → CTy → CTy
  #_      : CTy → CTy
\end{code}
Then comes the Meta-Language itself. It incorporates \AD{Tm} constructors
and eliminators with slightly different types: \emph{value} constructors
are associated to \emph{value} types whilst eliminators (and their branches)
have \emph{computational} types. Two new term constructors have been added:
\AIC{`ret} and \AIC{\_`>>=\_} make \AIC{\#\_} a monad. They can be used to
explicitly schedule the evaluation order of various subterms.
\begin{code}
data Ml : CTy → Cx CTy → Set where
  `var     : {σ : CTy} →    [ Var σ                    ⟶  Ml σ      ]
  _`$_     : {σ τ : CTy} →  [ Ml (σ `→# τ) ⟶ Ml σ      ⟶  Ml (# τ)  ]
  `⟨⟩      :                [                             Ml `1     ]
  `tt `ff  :                [                             Ml `2     ]
  `ret     : {σ : CTy} →    [ Ml σ                     ⟶  Ml (# σ)  ]
  _`>>=_   : {σ τ : CTy} →  [ Ml (# σ) ⟶ Ml (σ `→# τ)  ⟶  Ml (# τ)  ]
  `λ   : {σ τ : CTy} →      [ σ ⊢ Ml (# τ) ⟶  Ml (σ `→# τ)          ]
  `if  : {σ : CTy} → [ Ml `2 ⟶ Ml (# σ) ⟶ Ml (# σ) ⟶ Ml (# σ) ]
\end{code}
\AgdaHide{
\begin{code}
th^Ml : ∀ {σ} → Thinnable (Ml σ)
th^Ml ρ (`λ b)      = `λ (th^Ml (pop! ρ) b)
th^Ml ρ (`var v)    = `var (lookup ρ v)
th^Ml ρ (f `$ t)    = th^Ml ρ f `$ th^Ml ρ t
th^Ml ρ `⟨⟩         = `⟨⟩
th^Ml ρ `tt         = `tt
th^Ml ρ `ff         = `ff
th^Ml ρ (`if b l r) = `if (th^Ml ρ b) (th^Ml ρ l) (th^Ml ρ r)
th^Ml ρ (`ret t)    = `ret (th^Ml ρ t)
th^Ml ρ (t `>>= f)  = th^Ml ρ t `>>= th^Ml ρ f

map^Var : {ty ty′ : Set} {Γ : Cx ty} {σ : ty} → 
          (f : ty → ty′) → Var σ Γ → Var (f σ) (map^Cx f Γ)
map^Var f ze     = ze
map^Var f (su v) = su (map^Var f v)


map^Var-inv : {A B : Set} {Γ : Cx A} {τ : B} (f : A → B) →
              Var τ (map^Cx f Γ) → ∃ λ σ → τ ≡ f σ
map^Var-inv f = go _ PEq.refl where

  go : ∀ Γ {Δ τ} → map^Cx f Γ ≡ Δ → Var τ Δ → ∃ λ σ → τ ≡ f σ
  go ε       ()       ze
  go ε       ()       (su v)
  go (Γ ∙ _) PEq.refl ze     = , PEq.refl
  go (Γ ∙ _) PEq.refl (su v) = go Γ PEq.refl v


map⁻¹^Var : {A B : Set} {Γ : Cx A} {σ : A} {f : A → B} →
            (∀ {σ τ} → f σ ≡ f τ → σ ≡ τ) → Var (f σ) (map^Cx f Γ) → Var σ Γ
map⁻¹^Var {f = f} inj = go _ PEq.refl PEq.refl where

  go : ∀ Γ {σ τ Δ} → map^Cx f Γ ≡ Δ → f σ ≡ τ → Var τ Δ → Var σ Γ
  go ε       ()       eq ze
  go ε       ()       eq (su v)
  go (Γ ∙ σ) PEq.refl eq ze rewrite inj eq = ze
  go (Γ ∙ σ) PEq.refl eq (su v) = su (go Γ PEq.refl eq v)

map^⊆ : {A B : Set} {Γ Δ : Cx A} {f : A → B} →
        (∀ {σ τ} → f σ ≡ f τ → σ ≡ τ) → Γ ⊆ Δ → map^Cx f Γ ⊆ map^Cx f Δ
lookup (map^⊆ {f = f} f-inj inc) v =
  let (σ , eq) = map^Var-inv f v
      v₁       = map⁻¹^Var f-inj (PEq.subst (λ σ → Var σ _) eq v)
      v₂       = lookup inc v₁
      v₃       = map^Var f v₂
  in PEq.subst (λ σ → Var σ _) (PEq.sym eq) v₃

CBV : Ty → CTy
\end{code}}
As explained in Hatcliff and Danvy's paper, the translation from
\AD{Ty} to \AD{CTy} fixes the calling convention the CPS translation
will have. Both call by name (\AF{CBV}) and call by value (\AF{CBV})
can be encoded. They behave the same way on base types (and we group
the corresponding equations under the \AF{CBX} name) but differ in
case of the function space. In \AF{CBN} the argument of a function is
a computation whilst it is expected to have been fully evaluated in
\AF{CBV}.\vspace*{-1.5em}
\begin{code}
CBN : Ty → CTy
CBN `1        = `1
CBN `2        = `2
CBN (σ `→ τ)  = (#  CBN σ)  `→# CBN τ 
CBV (σ `→ τ)  =     CBV σ   `→# CBV τ
\end{code}
\AgdaHide{
\begin{code}
CBV `1        = `1
CBV `2        = `2

`→#-inj : ∀ {σ σ′ τ τ′} → σ `→# τ ≡ σ′ `→# τ′ → σ ≡ σ′ × τ ≡ τ′
`→#-inj PEq.refl = PEq.refl , PEq.refl

#-inj : ∀ {σ τ} → # σ ≡ # τ → σ ≡ τ
#-inj PEq.refl = PEq.refl

CBN-inj : ∀ σ τ → CBN σ ≡ CBN τ → σ ≡ τ
CBN-inj `1 `1 eq = PEq.refl
CBN-inj `1 `2 ()
CBN-inj `1 (τ `→ τ₁) ()
CBN-inj `2 `1 ()
CBN-inj `2 `2 eq = PEq.refl
CBN-inj `2 (τ `→ τ₁) ()
CBN-inj (σ `→ σ₁) `1 ()
CBN-inj (σ `→ σ₁) `2 ()
CBN-inj (σ `→ σ₁) (τ `→ τ₁) eq =
  let (eq₁ , eq₂) = `→#-inj eq in
  PEq.cong₂ _`→_ (CBN-inj _ _ (#-inj eq₁)) (CBN-inj _ _ eq₂)

CBV-inj : ∀ σ τ → CBV σ ≡ CBV τ → σ ≡ τ
CBV-inj `1 `1 eq = PEq.refl
CBV-inj `1 `2 ()
CBV-inj `1 (τ `→ τ₁) ()
CBV-inj `2 `1 ()
CBV-inj `2 `2 eq = PEq.refl
CBV-inj `2 (τ `→ τ₁) ()
CBV-inj (σ `→ σ₁) `1 ()
CBV-inj (σ `→ σ₁) `2 ()
CBV-inj (σ `→ σ₁) (τ `→ τ₁) eq =
  let (eq₁ , eq₂) = `→#-inj eq in
  PEq.cong₂ _`→_ (CBV-inj _ _ eq₁) (CBV-inj _ _ eq₂)

Ml^N : Model L.zero
Var^N : Model L.zero
Ml^V : Model L.zero
Var^V : Model L.zero
\end{code}}
From these translations, we can described the respective
interpretations of variables and terms for the two CPS
transformations. In both cases the return type of the
compiled term is a computational type: the source term is
a simple \AD{Tm} and as such can contain redexes. Variables
then play different roles: in the by name strategy, they
are all computations whereas in the by value one they are
expected to be evaluated already. This leads to the following
definitions:\vspace*{-1.5em}
\begin{code}
Var^N  σ Γ = Var  (# CBN σ)  (map^Cx (#_ ∘ CBN) Γ)
Ml^N   σ Γ = Ml   (# CBN σ)  (map^Cx (#_ ∘ CBN) Γ)
Var^V  σ Γ = Var  (CBV σ)    (map^Cx CBV Γ)
Ml^V   σ Γ = Ml   (# CBV σ)  (map^Cx CBV Γ)
\end{code}
Finally, the corresponding \AF{Semantics} can be defined (code
omitted here) and we get the two CPS transformations by creating
dummy environments to kickstart the evaluation:\vspace*{-1.5em}
\begin{code}
CPS^N : Semantics Var^N Ml^N
CPS^V : Semantics Var^V Ml^V
\end{code}\vspace*{-1.5em}
\AgdaHide{
\begin{code}
CPS^N = record
 { th     = λ σ → th^Var (# CBN σ) ∘ (map^⊆ (CBN-inj _ _ ∘ #-inj))
 ; ⟦var⟧  = `var
 ; ⟦λ⟧    = λ b → `ret (`λ (b (step refl) ze))
 ; _⟦$⟧_  = λ f t → f `>>= `λ (`var ze `$ th^Ml (step refl) t)
 ; ⟦⟨⟩⟧   = `ret `⟨⟩
 ; ⟦tt⟧   = `ret `tt
 ; ⟦ff⟧   = `ret `ff
 ; ⟦if⟧   = λ b l r → b `>>= `λ (`if (`var ze) (th^Ml (step refl) l) (th^Ml (step refl) r)) }
CPS^V = record
 { th     = λ σ → th^Var (CBV σ) ∘ map^⊆ (CBV-inj _ _)
 ; ⟦var⟧  = `ret ∘ `var
 ; ⟦λ⟧    = λ b → `ret (`λ (b (step refl) ze))
 ; _⟦$⟧_  = λ f t → f `>>= `λ (th^Ml (step refl) t `>>= `λ (`var (su ze) `$ `var ze))
 ; ⟦⟨⟩⟧   = `ret `⟨⟩
 ; ⟦tt⟧   = `ret `tt
 ; ⟦ff⟧   = `ret `ff
 ; ⟦if⟧   = λ b l r → b `>>= `λ (`if (`var ze) (th^Ml (step refl) l) (th^Ml (step refl) r)) }
\end{code}}
\begin{code}
cps^N : {σ : Ty} → [ Tm σ ⟶ Ml^N σ ]
cps^N = let open Eval CPS^N in sem dummy
  where dummy = pack (map^Var (#_ ∘ CBN))
cps^V : {σ : Ty} → [ Tm σ ⟶ Ml^V σ ]
cps^V = let open Eval CPS^V in sem dummy
  where dummy = pack (map^Var CBV)
\end{code}

\section{Proving Properties of Semantics}
\label{properties}

Thanks to \AF{Semantics}, we have already saved work by not reiterating the same traversals.
Moreover, this disciplined approach to building models and
defining the associated evaluation functions can help us refactor
the proofs of some properties of these semantics.

Instead of using proof scripts as Benton et al.~(\citeyear{benton2012strongly})
do, we describe abstractly the constraints the logical relations~\cite{reynolds1983types}
defined on computations (and environment values) have to respect to ensure
that evaluating a term in related environments
produces related outputs. This gives us a generic framework to
state and prove, in one go, properties about all of these semantics.

Our first example of such a framework will stay simple on purpose.
However it is no mere bureaucracy: the
result proven here will actually be useful in the next section
when considering more complex properties.

\subsection{The Simulation Relation}

This first example is describing the relational interpretation
of the terms. It should give the reader a good introduction to
the setup before we take on more complexity. The types
involved might look a bit scarily abstract but the idea is rather simple:
we have a \AR{Simulation} between
two \AR{Semantics} when evaluating a term in related environments yields
related values. The bulk of the work is to make this intuition formal.

The evidence that we have a \AR{Simulation} between two \AR{Semantics} is
packaged in a record indexed by the semantics as well as two relations.
We call \AF{RModel} (for \emph{R}elational \emph{Model}) the type of these
relations; the first one (\AB{𝓥^R}) relates values in the respective environments
and the second one (\AB{𝓒^R}) describes simulation for computations.
\AgdaHide{
\begin{code}
record RModel {ℓ^E ℓ^M : Level} (𝓥 : Model ℓ^E) (𝓒 : Model ℓ^M) (ℓ^R : Level) : Set (ℓ^E ⊔ ℓ^M ⊔ L.suc ℓ^R) where
  constructor mkRModel
  field rmodel : {σ : Ty} → [ 𝓥 σ ⟶ 𝓒 σ ⟶ const (Set ℓ^R) ]
open RModel public


record `∀[_] {ℓ^A ℓ^B ℓ^R : Level} {𝓥^A : Model ℓ^A} {𝓥^B : Model ℓ^B}
             (𝓥^R : RModel 𝓥^A 𝓥^B ℓ^R)
             {Γ Δ : Cx Ty} (ρ^A : (Γ -Env) 𝓥^A Δ) (ρ^B : (Γ -Env) 𝓥^B Δ) : Set ℓ^R where
  constructor pack^R
  field lookup^R : {σ : Ty} (v : Var σ Γ) → rmodel 𝓥^R (lookup ρ^A v) (lookup ρ^B v)
open `∀[_]
\end{code}}
\begin{code}
record Simulation {ℓ^EA ℓ^MA ℓ^EB ℓ^MB ℓ^RE ℓ^RM : Level} {𝓥^A : Model ℓ^EA} {𝓒^A : Model ℓ^MA} {𝓥^B : Model ℓ^EB} {𝓒^B : Model ℓ^MB}
  (𝓢^A : Semantics 𝓥^A 𝓒^A) (𝓢^B : Semantics 𝓥^B 𝓒^B)
  (𝓥^R  : RModel 𝓥^A 𝓥^B ℓ^RE) (𝓒^R  : RModel 𝓒^A 𝓒^B ℓ^RM) : Set (ℓ^RE ⊔ ℓ^RM ⊔ ℓ^EA ⊔ ℓ^EB ⊔ ℓ^MA ⊔ ℓ^MB) where
\end{code}
\AgdaHide{
\begin{code}
 module 𝓢^A = Semantics 𝓢^A
 module 𝓢^B = Semantics 𝓢^B
 sem^A = Eval.sem 𝓢^A
 sem^B = Eval.sem 𝓢^B
 field
\end{code}}

The record's fields say what structure these relations
need to have. \ARF{𝓥^R‿th} states that two similar environments
can be thinned whilst staying in simulation. It is stated using the
\AF{`∀[\_]} predicate transformer (omitted here) which lifts \AB{𝓥^R}
to contexts in a pointwise manner.
\begin{code}
  𝓥^R‿th  :  {Γ Δ Θ : Cx Ty} (inc : Δ ⊆ Θ) {ρ^A : (Γ -Env) 𝓥^A Δ} {ρ^B : (Γ -Env) 𝓥^B Δ} → `∀[ 𝓥^R ] ρ^A ρ^B →
             `∀[ 𝓥^R ] (th[ 𝓢^A.th ] inc ρ^A) (th[ 𝓢^B.th ] inc ρ^B)
\end{code}

We then have the relational counterparts of the term constructors.
To lighten the presentation we introduce \AF{𝓡}, which states that
the evaluation of a term in distinct contexts yields related computations.
And we focus on the most interesting combinators, giving only one
characteristic example of the remaining ones.
\begin{code}
 𝓡 : {Γ Δ : Cx Ty} {σ : Ty} → Tm σ Γ → (Γ -Env) 𝓥^A Δ → (Γ -Env) 𝓥^B Δ → Set ℓ^RM
 𝓡 t ρ^A ρ^B = rmodel 𝓒^R (sem^A ρ^A t) (sem^B ρ^B t)
\end{code}
\AgdaHide{
\begin{code}
 field
\end{code}}

Our first interesting case is the relational counterpart of \AIC{`var}:
a variable evaluated in two related environments yields related computations.
In other words \ARF{⟦var⟧} turns related values in related computations.
\begin{code}
  R⟦var⟧    :  {Γ Δ : Cx Ty} {σ : Ty} (v : Var σ Γ) {ρ^A : (Γ -Env) 𝓥^A Δ} {ρ^B : (Γ -Env) 𝓥^B Δ} → `∀[ 𝓥^R ] ρ^A ρ^B → 𝓡 (`var v) ρ^A ρ^B
\end{code}
The second, and probably most interesting case, is the relational counterpart
to the \ARF{⟦λ⟧} combinator. The ability to evaluate the body of a \AIC{`λ} in
thinned environments, each extended by related values, and deliver similar
values is enough to guarantee that evaluating the $\lambda$s in the original
environments will produce similar values.
\begin{code}
  R⟦λ⟧ :  {Γ Δ : Cx Ty} {σ τ : Ty} {b : Tm τ (Γ ∙ σ)} {ρ^A : (Γ -Env) 𝓥^A Δ} {ρ^B : (Γ -Env) 𝓥^B Δ} (r :  {Θ : Cx Ty} {u^A : 𝓥^A σ Θ} {u^B : 𝓥^B σ Θ} → ∀ inc → rmodel 𝓥^R u^A u^B →
                    let  ρ^A′ = th[ 𝓢^A.th ] inc ρ^A `∙ u^A
                         ρ^B′ = th[ 𝓢^B.th ] inc ρ^B `∙ u^B
                    in 𝓡 b ρ^A′ ρ^B′) →
          `∀[ 𝓥^R ] ρ^A ρ^B → 𝓡 (`λ b) ρ^A ρ^B
\end{code}
All the remaining cases follow suit: assuming that the evaluation of
subterms produces related computations and that the current environments
are related, we conclude that the evaluation of the whole term should
yield related computations. We show here the relational counterpart of
the application constructor and omit the remaining ones:
\begin{code}
  R⟦$⟧  :  {Γ Δ : Cx Ty} {σ τ : Ty} {f : Tm (σ `→ τ) Γ} {t : _} {ρ^A : (Γ -Env) 𝓥^A Δ} {ρ^B : _} → 𝓡 f ρ^A ρ^B → 𝓡 t ρ^A ρ^B →
           `∀[ 𝓥^R ] ρ^A ρ^B → 𝓡 (f `$ t) ρ^A ρ^B
\end{code}
\AgdaHide{
\begin{code}
  R⟦⟨⟩⟧ :  {Γ Δ : Cx Ty} {ρ^A : (Γ -Env) 𝓥^A Δ} {ρ^B : _} → `∀[ 𝓥^R ] ρ^A ρ^B → 𝓡 `⟨⟩ ρ^A ρ^B
  R⟦tt⟧ :  {Γ Δ : Cx Ty} {ρ^A : (Γ -Env) 𝓥^A Δ} {ρ^B : _} → `∀[ 𝓥^R ] ρ^A ρ^B → 𝓡 `tt ρ^A ρ^B
  R⟦ff⟧ :  {Γ Δ : Cx Ty} {ρ^A : (Γ -Env) 𝓥^A Δ} {ρ^B : _} → `∀[ 𝓥^R ] ρ^A ρ^B → 𝓡 `ff ρ^A ρ^B
  R⟦if⟧ :  {Γ Δ : Cx Ty} {σ : Ty} {b : _} {l r : Tm σ Γ} {ρ^A : (Γ -Env) 𝓥^A Δ} {ρ^B : _} → 𝓡 b ρ^A ρ^B → 𝓡 l ρ^A ρ^B → 𝓡 r ρ^A ρ^B →
             `∀[ 𝓥^R ] ρ^A ρ^B → 𝓡 (`if b l r) ρ^A ρ^B
infixl 10 _∙^R_
\end{code}}
This specification is only useful if some semantics satisfy it and if given
that these constraints are satisfied we can prove the fundamental lemma of
simulations stating that the evaluation of a term on related inputs yields
related output.

\begin{theorem}[Fundamental Lemma of Simulations]
Given two Semantics \AB{𝓢^A} and \AB{𝓢^B} in simulation with respect to
relations \AB{𝓥^R} for values and \AB{𝓒^R} for computations, we have:

For any term \AB{t} and environments \AB{ρ^A} and \AB{ρ^B}, if the two environments
are \AB{𝓥^R}-related in a pointwise manner then the semantics associated
to \AB{t} by \AB{𝓢^A} using \AB{ρ^A} is \AB{𝓒^R}-related to the one associated to
\AB{t} by \AB{𝓢^B} using \AB{ρ^B}.
\end{theorem}
\begin{proof}The proof is a structural induction on \AB{t} like the
one used to define \AF{sem}. It uses the combinators provided by
the constraint that \AB{𝓢^A} and \AB{𝓢^B} are in simulation to make use of the
induction hypotheses.
\end{proof}

% We introduce a \AM{Simulate} module
% parametrised by a record packing the evidence that two semantics are in \AR{Simulation}. % This allows us to bring all of the corresponding relational
% counterpart of term constructors into scope by \AK{open}ing the record. The
% traversal then uses them to combine the induction hypotheses arising structurally.
% We use \AF{[\_,\_,\_]\_∙^R\_} as a way to circumvent Agda's inhability to
% infer \AR{𝓥^A}, \AR{𝓥^B} and \AR{𝓥^R}.

\AgdaHide{
\begin{code}
_∙^R_ :  {ℓ^EA ℓ^EB ℓ^ER : Level} {𝓥^A : Model ℓ^EA} {𝓥^B : Model ℓ^EB} {𝓥^R : RModel 𝓥^A 𝓥^B ℓ^ER} {Δ Γ : Cx Ty} {ρ^A : (Γ -Env) 𝓥^A Δ} {ρ^B : (Γ -Env) 𝓥^B Δ} {σ : Ty} {u^A : 𝓥^A σ Δ} {u^B : _} → `∀[ 𝓥^R ] ρ^A ρ^B → rmodel 𝓥^R u^A u^B → `∀[ 𝓥^R ] (ρ^A `∙ u^A) (ρ^B `∙ u^B)
lookup^R (ρ^R ∙^R u^R) ze    = u^R
lookup^R (ρ^R ∙^R u^R) (su v)  = lookup^R ρ^R v

module Simulate {ℓ^EA ℓ^MA ℓ^EB ℓ^MB : Level} {𝓥^A : Model ℓ^EA} {𝓒^A : Model ℓ^MA} {𝓢^A : Semantics 𝓥^A 𝓒^A} {𝓥^B : Model ℓ^EB} {𝓒^B : Model ℓ^MB} {𝓢^B : Semantics 𝓥^B 𝓒^B} {ℓ^RE ℓ^RM : Level} {𝓥^R : RModel 𝓥^A 𝓥^B ℓ^RE} {𝓒^R : RModel 𝓒^A 𝓒^B ℓ^RM} (𝓡 : Simulation 𝓢^A 𝓢^B 𝓥^R 𝓒^R) where
  open Simulation 𝓡
\end{code}\vspace*{ -2.5em}
%<*relational>
\begin{code}
  sim :  {Γ Δ : Cx Ty} {σ : Ty} (t : Tm σ Γ) {ρ^A : (Γ -Env) 𝓥^A Δ} {ρ^B : (Γ -Env) 𝓥^B Δ} (ρ^R : `∀[ 𝓥^R ] ρ^A ρ^B) →
       rmodel 𝓒^R (sem^A ρ^A t) (sem^B ρ^B t)
  sim (`var v)     ρ^R = R⟦var⟧ v ρ^R
  sim (f `$ t)     ρ^R = R⟦$⟧ {f = f} {t} (sim f ρ^R) (sim t ρ^R) ρ^R
  sim (`λ t)       ρ^R = R⟦λ⟧ {b = t} (λ inc u^R → sim t (𝓥^R‿th inc ρ^R ∙^R u^R)) ρ^R
  sim `⟨⟩          ρ^R = R⟦⟨⟩⟧ ρ^R
  sim `tt          ρ^R = R⟦tt⟧ ρ^R
  sim `ff          ρ^R = R⟦ff⟧ ρ^R
  sim (`if b l r)  ρ^R = R⟦if⟧ {b = b} {l} {r} (sim b ρ^R) (sim l ρ^R) (sim r ρ^R) ρ^R
\end{code}
%</relational>
}

\begin{corollary}[Renaming is a Substitution]Applying a renaming \AB{ρ} to
a term $t$ amounts to applying the substitution  \AF{map^Env} \AIC{`var} \AB{ρ}
to that same term $t$.
\end{corollary}
\begin{proof}This is shown by instantiating the fundamental lemma of
simulations for the special case where: \AB{𝓢^A} is \AF{Renaming},
\AB{𝓢^B} is \AF{Substitution}, {\AB{𝓥^R} \AB{v} \AB{t}} is
{\AIC{`var} \AB{v} \AD{≡} \AB{t}} (in other words: the terms in the
substitution are precisely the variables in the renaming), and
\AB{𝓒^R} is propositional equality.

The constraints corresponding to the various combinators are mundane:
propositional equality is a congruence.
\end{proof}
\AgdaHide{
\begin{code}
SimulationRenamingSubstitution :  Simulation Renaming Substitution
                                      (mkRModel (_≡_ ∘ `var)) (mkRModel _≡_)
SimulationRenamingSubstitution =
  record
    { 𝓥^R‿th  = λ inc ρ^R → pack^R (PEq.cong (th^Tm _ inc) ∘ lookup^R ρ^R)
    ; R⟦var⟧   = λ v ρ^R → lookup^R ρ^R v
    ; R⟦$⟧     = λ eqf eqt _ → PEq.cong₂ _`$_ eqf eqt
    ; R⟦λ⟧     = λ r _ → PEq.cong `λ (r (step refl) PEq.refl)
    ; R⟦⟨⟩⟧    = λ _ → PEq.refl
    ; R⟦tt⟧    = λ _ → PEq.refl
    ; R⟦ff⟧    = λ _ → PEq.refl
    ; R⟦if⟧    = λ eqb eql eqr _ → PEq.cong₂ (uncurry `if) (PEq.cong₂ _,_ eqb eql) eqr
    }
\end{code}
\begin{code}
rensub : {Γ Δ : Cx Ty} {σ : Ty} → ∀ t ρ → th^Tm σ {Γ} {Δ} ρ t ≡ subst (map^Env `var ρ) t
rensub t ρ = sim t (pack^R (λ _ → PEq.refl))
  where open Simulate SimulationRenamingSubstitution
\end{code}}

Another corollary of the simulation lemma relates NBE to itself. This may
seem bureaucratic but it is crucial: the model definition \AF{Kr}
uses the host language's function space which contains more functions than
simply the ones obtained by evaluating a $λ$-term. These exotic functions have
undesirable behaviours and need to be ruled out to ensure that
normalisation has good properties. This is done by defining a Partial
Equivalence Relation~\cite{mitchell1996foundations} (PER) on the model: the
elements equal to themselves will be guaranteed to be well behaved. We
show that given an environment of values PER-related to themselves,
the evaluation of a $λ$-term produces a computation equal to itself too.

We start by defining the PER for the model. It is constructed
by induction on the type and ensures that terms which behave the same
extensionally are declared equal. Two values of type \AIC{`1} are
always trivially equal;  values of type \AIC{`2} are normal forms
and are declared equal when they are effectively syntactically the same;
finally functions are equal whenever equal inputs map to equal
outputs.\vspace*{ -1em}
\AgdaHide{
\begin{code}
open βιξη
\end{code}}
\begin{code}
PER : (σ : Ty) → [ Kr σ ⟶ Kr σ ⟶ const Set ]
PER `1        T U = ⊤
PER `2        T U = T ≡ U
PER (σ `→ τ)  T U =  {Δ : Cx Ty} {V W : Kr σ Δ} → ∀ inc → PER σ V W →
                     PER τ (T inc V) (U inc W)
\end{code}
\AgdaHide{
\begin{code}
PER′ : RModel Kr Kr L.zero
PER′ = mkRModel (λ {σ} → PER σ)

PropEq : {C : Model L.zero} → RModel C C L.zero
PropEq = mkRModel _≡_
\end{code}}

It is indeed a PER as witnessed by the (omitted here) proofs that
\AF{PER} \AB{σ} is symmetric and transitive. It also respects the
notion of thinning defined for \AF{Kr}.
\begin{code}
sym^PER : {Γ : Cx Ty} (σ : Ty) {S T : Kr σ Γ} → PER σ S T → PER σ T S
\end{code}
\AgdaHide{
\begin{code}
sym^PER `1     eq = ⟨⟩
sym^PER `2     eq = PEq.sym eq
sym^PER (σ `→ τ)  eq = λ inc eqVW → sym^PER τ (eq inc (sym^PER σ eqVW))
\end{code}}\vspace*{ -2.5em}%ugly but it works!
\begin{code}
trans^PER : {Γ : Cx Ty} (σ : Ty) {S T U : Kr σ Γ} → PER σ S T → PER σ T U → PER σ S U
\end{code}
\AgdaHide{
\begin{code}
  -- We are in PER so refl^PER is not provable
  -- but as soon as PER σ V W then PER σ V V
refl^PER : {Γ : Cx Ty} (σ : Ty) {S T : Kr σ Γ} → PER σ S T → PER σ S S

trans^PER `1     eq₁ eq₂ = ⟨⟩
trans^PER `2     eq₁ eq₂ = PEq.trans eq₁ eq₂
trans^PER (σ `→ τ)  eq₁ eq₂ =
  λ inc eqVW → trans^PER τ (eq₁ inc (refl^PER σ eqVW)) (eq₂ inc eqVW)

refl^PER σ eq = trans^PER σ eq (sym^PER σ eq)
\end{code}}\vspace*{ -2.5em}%ugly but it works!
\begin{code}
th^PER :  {Δ Γ : Cx Ty} (σ : Ty) (inc : Γ ⊆ Δ) {T U : Kr σ Γ} → PER σ T U → PER σ (th^Kr σ inc T) (th^Kr σ inc U)
\end{code}
\AgdaHide{
\begin{code}
th^PER `1     inc eq = ⟨⟩
th^PER `2     inc eq = PEq.cong (th^nf `2 inc) eq
th^PER (σ `→ τ)  inc eq = λ inc′ eqVW → eq (select inc inc′) eqVW
\end{code}}

The interplay of reflect and reify with this notion of equality has
to be described in one go because of their mutual definition.
It confirms that \AF{PER} is an appropriate notion of
semantic equality: \AF{PER}-related values are reified to propositionally
equal normal forms whilst propositionally equal neutral terms are reflected
to \AF{PER}-related values.\vspace*{ -1em}
\begin{code}
reify^PER    :  {Γ : Cx Ty} (σ : Ty) {T U : Kr σ Γ} → PER σ T U → reify σ T ≡ reify σ U
reflect^PER  :  {Γ : Cx Ty} (σ : Ty) {t u : Ne σ Γ} → t ≡ u → PER σ (reflect σ t) (reflect σ u)
\end{code}
\AgdaHide{
\begin{code}
reify^PER `1     EQTU = PEq.refl
reify^PER `2     EQTU = EQTU
reify^PER (σ `→ τ)  EQTU = PEq.cong `λ (reify^PER τ (EQTU (step refl) (reflect^PER σ PEq.refl)))

reflect^PER `1     eq = ⟨⟩
reflect^PER `2     eq = PEq.cong (`ne _) eq
reflect^PER (σ `→ τ)  eq = λ inc rel → reflect^PER τ (PEq.cong₂ _`$_ (PEq.cong (th^ne (σ `→ τ) inc) eq) (reify^PER σ rel))

ifRelNorm :
      let open Semantics Normalise in
      {σ : Ty} {Γ : Cx Ty} {b^A b^B : Kr `2 Γ} {l^A l^B r^A r^B : Kr σ Γ} →
      PER `2 b^A b^B → PER σ l^A l^B → PER σ r^A r^B →
      PER σ {Γ} (⟦if⟧ {σ} b^A l^A r^A) (⟦if⟧ {σ} b^B l^B r^B)
ifRelNorm {b^A = `tt}             PEq.refl l^R r^R = l^R
ifRelNorm {b^A = `ff}             PEq.refl l^R r^R = r^R
ifRelNorm {σ} {b^A = `ne _ ne} PEq.refl l^R r^R =
  reflect^PER σ (PEq.cong₂ (`if ne) (reify^PER σ l^R) (reify^PER σ r^R))
\end{code}}

That suffices to show that evaluating a term in two
environments related pointwise by \AF{PER}
yields two semantic objects themselves related by \AF{PER}.

\begin{corollary}[No exotic values]The evaluation of a term $t$
in an environment of values equal to themselves according to \AF{PER}
yields a value equal to itself according to \AF{PER}
\end{corollary}
\begin{proof}By the fundamental lemma of simulations with \AB{𝓢^A} and
\AB{𝓢^B} equal to \AF{Normalise}, \AB{𝓥^R} and \AB{𝓒^R} to \AF{PER}.
\end{proof}
\AgdaHide{
%<*synchroexample>
\begin{code}
SimulationNormalise :  Simulation Normalise Normalise PER′ PER′
\end{code}
%</synchroexample>
\begin{code}
SimulationNormalise =
  record  { 𝓥^R‿th  = λ inc ρ^R → pack^R (th^PER _ inc ∘ lookup^R ρ^R)
          ; R⟦var⟧   = λ v ρ^R → lookup^R ρ^R v
          ; R⟦$⟧     = λ f t _ → f refl t
          ; R⟦λ⟧     = λ r _ inc eq → r inc eq
          ; R⟦⟨⟩⟧    = λ _ → ⟨⟩
          ; R⟦tt⟧    = λ _ → PEq.refl
          ; R⟦ff⟧    = λ _ → PEq.refl
          ; R⟦if⟧    = λ eqb eql eqr _ → ifRelNorm eqb eql eqr
          }
\end{code}}

We can move on to the more complex example of a proof
framework built generically over our notion of \AF{Semantics}

\subsection{Fusions of Evaluations}

When studying the meta-theory of a calculus, one systematically
needs to prove fusion lemmas for various semantics. For instance,
Benton et al.~(\citeyear{benton2012strongly}) prove six such lemmas
relating renaming, substitution and a typeful semantics embedding
their calculus into Coq. This observation naturally led us to
defining a fusion framework describing how to relate three semantics:
the pair we sequence and their sequential composition. The fundamental
lemma we prove can then be instantiated six times
to derive the corresponding corollaries.

The evidence that \AB{𝓢^A}, \AB{𝓢^B} and \AB{𝓢^C} are such
that \AB{𝓢^A} followed by \AB{𝓢^B} is equivalent
to \AB{𝓢^C} (e.g. \AF{Substitution} followed by \AF{Renaming}
can be reduced to \AF{Substitution}) is packed in a record
\AR{Fusable} indexed by the three semantics but also three
relations. The first one (\AB{𝓥^R_{BC}}) states what it means
for two environment values of \AB{𝓢^B} and \AB{𝓢^C} respectively
to be related. The second one (\AB{𝓥^R}) characterises the triples
of environments (one for each one of the semantics) which are
compatible. The last one (\AB{𝓒^R}) relates values
in \AB{𝓢^B} and \AB{𝓢^C}'s models.
\begin{code}
record Fusable {ℓ^EA ℓ^MA ℓ^EB ℓ^MB ℓ^EC ℓ^MC ℓ^RE ℓ^REBC ℓ^RM : Level} {𝓥^A : Model ℓ^EA} {𝓥^B : Model ℓ^EB} {𝓥^C : Model ℓ^EC} {𝓒^A : Model ℓ^MA} {𝓒^B : Model ℓ^MB} {𝓒^C : Model ℓ^MC} (𝓢^A : Semantics 𝓥^A 𝓒^A)
 (𝓢^B : Semantics 𝓥^B 𝓒^B) (𝓢^C : Semantics 𝓥^C 𝓒^C)
 (𝓥^R‿BC : RModel 𝓥^B 𝓥^C ℓ^REBC)
 (𝓥^R :  {Θ Δ Γ : Cx Ty} → (Γ -Env) 𝓥^A Δ → (Δ -Env) 𝓥^B Θ →
         (Γ -Env) 𝓥^C Θ → Set ℓ^RE)
 (𝓒^R : RModel 𝓒^B 𝓒^C ℓ^RM) : Set (ℓ^RM ⊔ ℓ^RE ⊔ ℓ^EC ⊔ ℓ^EB ⊔ ℓ^EA ⊔ ℓ^MA ⊔ ℓ^REBC) where
\end{code}
\AgdaHide{
\begin{code}
 module 𝓢^A = Semantics 𝓢^A
 module 𝓢^B = Semantics 𝓢^B
 module 𝓢^C = Semantics 𝓢^C
 sem^A = Eval.sem 𝓢^A
 sem^B = Eval.sem 𝓢^B
 sem^C = Eval.sem 𝓢^C
 field
\end{code}}

As before, most of the fields of this record describe
what structure these relations need to have. However, we start with something
slightly different: given that we are planing to run the \AR{Semantics} \AB{𝓢^B}
\emph{after} having run \AB{𝓢^A}, we need two components: a way to extract a
term from an \AB{𝓢^A} and a way to manufacture a dummy \AB{𝓢^A} value when
going under a binder. Our first two fields are therefore:
\begin{code}
  reify^A    : {σ : Ty} → [  𝓒^A σ ⟶ Tm σ  ]
  var‿0^A    : {σ : Ty} → [  σ ⊢ 𝓥^A σ     ]
\end{code}
Then come two constraints dealing with the relations talking
about evaluation environments. \ARF{𝓥^R‿∙} tells us how to
extend related environments: one should be able to push related
values onto the environments for \AB{𝓢^B} and \AB{𝓢^C} whilst
merely extending the one for \AB{𝓢^A} with the token value \ARF{var‿0^A}.

\ARF{𝓥^R‿th} guarantees that it is always possible to thin
the environments for \AB{𝓢^B} and \AB{𝓢^C} in a \AB{𝓥^R}
preserving manner.\vspace*{ -1em}
\begin{code}
  𝓥^R‿∙   :  {Γ Δ Θ : Cx Ty} {σ : Ty} {ρ^A : (Γ -Env) 𝓥^A Δ} {ρ^B : (Δ -Env) 𝓥^B Θ} {ρ^C : (Γ -Env) 𝓥^C Θ} {u^B : 𝓥^B σ Θ} {u^C : 𝓥^C σ Θ} → 𝓥^R ρ^A ρ^B ρ^C → rmodel 𝓥^R‿BC u^B u^C →
             let ρ^A′ = th[ 𝓢^A.th ] (step refl) ρ^A `∙ var‿0^A
             in 𝓥^R ρ^A′ (ρ^B `∙ u^B) (ρ^C `∙ u^C)
\end{code}\vspace*{ -1.75em}
\begin{code}
  𝓥^R‿th  :  {Γ Δ Θ E : Cx Ty} (inc : Θ ⊆ E) {ρ^A : (Γ -Env) 𝓥^A Δ} {ρ^B : (Δ -Env) 𝓥^B Θ} {ρ^C : (Γ -Env) 𝓥^C Θ} → 𝓥^R ρ^A ρ^B ρ^C →
             𝓥^R ρ^A (th[ 𝓢^B.th ] inc ρ^B) (th[ 𝓢^C.th ] inc ρ^C)
\end{code}
Then we have the relational counterpart of the various term constructors.
We can once more introduce an extra definition \AF{𝓡} which will make the type
of the combinators defined later on clearer. \AF{𝓡} relates a term and three
environments by stating that the computation one gets by sequentially evaluating
the term in the first and then the second environment is related to the one
obtained by directly evaluating the term in the third environment.
\AgdaHide{
\begin{code}
 𝓡 : {σ : Ty} {Γ Δ Θ : Cx Ty} → Tm σ Γ → (Γ -Env) 𝓥^A Δ → (Δ -Env) 𝓥^B Θ → (Γ -Env) 𝓥^C Θ → Set _
\end{code}}
\begin{code}
 𝓡 t ρ^A ρ^B ρ^C = rmodel 𝓒^R  (sem^B ρ^B (reify^A (sem^A ρ^A t)))
                               (sem^C ρ^C t)
\end{code}
\AgdaHide{
\begin{code}
 field
\end{code}}
As with the previous section, only a handful of these combinators are out
of the ordinary. We will start with the \AIC{`var} case. It states that
fusion indeed happens when evaluating a variable using related environments.
\begin{code}
  R⟦var⟧  :  {Γ Δ Θ : Cx Ty} {σ : Ty} {ρ^A : (Γ -Env) 𝓥^A Δ} {ρ^B : (Δ -Env) 𝓥^B Θ} {ρ^C : (Γ -Env) 𝓥^C Θ} → ∀ v → 𝓥^R ρ^A ρ^B ρ^C → 𝓡 {σ} (`var v) ρ^A ρ^B ρ^C
\end{code}

The \AIC{`λ}-case puts some rather strong restrictions on the way
the $λ$-abstraction's body may be used by \AB{𝓢^A}: we assume it
is evaluated in an environment thinned by one variable and extended
using \ARF{var‿0^A}. But it is quite natural to have these restrictions:
given that \ARF{reify^A} quotes the result back, we are expecting this
type of evaluation in an extended context (i.e. under one lambda). And
it turns out that this is indeed enough for all of our examples.
The evaluation environments used by the semantics \AB{𝓢^B} and \AB{𝓢^C}
on the other hand can be arbitrarily thinned before being extended with
related values to be substituted for the variable bound by the \AIC{`λ}.\vspace*{ -1em}

\begin{code}
  R⟦λ⟧    :  {Γ Δ Θ : Cx Ty} {σ τ : Ty} {ρ^A : (Γ -Env) 𝓥^A Δ} {ρ^B : (Δ -Env) 𝓥^B Θ} {ρ^C : (Γ -Env) 𝓥^C Θ} (t : Tm τ (Γ ∙ σ))
             (r :  {E : Cx Ty} {u^B : 𝓥^B σ E} {u^C : 𝓥^C σ E} → ∀ inc → rmodel 𝓥^R‿BC u^B u^C →
                   let  ρ^A′ =  th[ 𝓢^A.th ] (step refl) ρ^A `∙ var‿0^A
                        ρ^B′ =  th[ 𝓢^B.th ] inc ρ^B `∙ u^B
                        ρ^C′ =  th[ 𝓢^C.th ] inc ρ^C `∙ u^C
                   in 𝓡 t ρ^A′ ρ^B′ ρ^C′) →
             𝓥^R ρ^A ρ^B ρ^C → 𝓡 (`λ t) ρ^A ρ^B ρ^C
\end{code}
The other cases (omitted here) are just stating that, given
the expected induction hypotheses, and the assumption that the three
environments are \AB{𝓥^R}-related we can deliver a proof that fusion
can happen on the compound expression.
\AgdaHide{
\begin{code}
  R⟦$⟧    : {Γ Δ Θ : Cx Ty} {σ τ : Ty} (f : Tm (σ `→ τ) Γ) (t : Tm σ Γ)
            {ρ^A : (Γ -Env) 𝓥^A Δ} {ρ^B : (Δ -Env) 𝓥^B Θ} {ρ^C : (Γ -Env) 𝓥^C Θ} →
            𝓡 f ρ^A ρ^B ρ^C → 𝓡 t ρ^A ρ^B ρ^C →
            𝓥^R ρ^A ρ^B ρ^C → 𝓡 (f `$ t) ρ^A ρ^B ρ^C
  R⟦⟨⟩⟧   : {Γ Δ Θ : Cx Ty} {ρ^A : (Γ -Env) 𝓥^A Δ} {ρ^B : (Δ -Env) 𝓥^B Θ} {ρ^C : (Γ -Env) 𝓥^C Θ} → 𝓥^R ρ^A ρ^B ρ^C → 𝓡 `⟨⟩ ρ^A ρ^B ρ^C
  R⟦tt⟧   : {Γ Δ Θ : Cx Ty} {ρ^A : (Γ -Env) 𝓥^A Δ} {ρ^B : (Δ -Env) 𝓥^B Θ} {ρ^C : (Γ -Env) 𝓥^C Θ} → 𝓥^R ρ^A ρ^B ρ^C → 𝓡 `tt ρ^A ρ^B ρ^C
  R⟦ff⟧   : {Γ Δ Θ : Cx Ty} {ρ^A : (Γ -Env) 𝓥^A Δ} {ρ^B : (Δ -Env) 𝓥^B Θ} {ρ^C : (Γ -Env) 𝓥^C Θ} → 𝓥^R ρ^A ρ^B ρ^C → 𝓡 `ff ρ^A ρ^B ρ^C
  R⟦if⟧ : {Γ Δ Θ : Cx Ty} {σ : Ty} (b : Tm `2 Γ) (l r : Tm σ Γ)
            {ρ^A : (Γ -Env) 𝓥^A Δ} {ρ^B : (Δ -Env) 𝓥^B Θ} {ρ^C : (Γ -Env) 𝓥^C Θ} →
            𝓥^R ρ^A ρ^B ρ^C →
            𝓡 b ρ^A ρ^B ρ^C →
            𝓡 l ρ^A ρ^B ρ^C →
            𝓡 r ρ^A ρ^B ρ^C →
            𝓡 (`if b l r) ρ^A ρ^B ρ^C
\end{code}}

As with simulation, we measure the utility of this framework
by the way we can prove its fundamental lemma and then
obtain useful corollaries. Once again, having carefully
identified what the constraints should be, proving the fundamental lemma
is not a problem:

\begin{theorem}[Fundamental Lemma of Fusable Semantics]
Given three Semantics \AB{𝓢^A}, \AB{𝓢^B} and \AB{𝓢^C} which are fusable
with respect to the relations \AB{𝓥^R‿BC} for values of \AB{𝓢^B} and \AB{𝓢^C},
\AB{𝓥^R} for environemnts and \AB{𝓒^R} for computations, we have that:

For any term \AB{t} and environments \AB{ρ^A}, \AB{ρ^B}, and \AB{ρ^C}, if the
three environments are \AB{𝓥^R}-related then the semantics associated to \AB{t}
by \AB{𝓢^A} using \AB{ρ^A} followed by \AB{𝓢^B} using \AB{ρ^B} is \AB{𝓒^R}-related
to the one associated to \AB{t} by \AB{𝓢^C} using \AB{ρ^C}.
\end{theorem}
\begin{proof} The proof is by structural induction on \AB{t} using the
combinators to assemble the induction hypotheses.
\end{proof}
\AgdaHide{
\begin{code}
module Fusion {ℓ^EA ℓ^MA ℓ^EB ℓ^MB ℓ^EC ℓ^MC ℓ^RE ℓ^REB ℓ^RM : Level} {𝓥^A : Model ℓ^EA} {𝓥^B : Model ℓ^EB} {𝓥^C : Model ℓ^EC} {𝓒^A : Model ℓ^MA} {𝓒^B : Model ℓ^MB} {𝓒^C : Model ℓ^MC} {𝓢^A : Semantics 𝓥^A 𝓒^A} {𝓢^B : Semantics 𝓥^B 𝓒^B} {𝓢^C : Semantics 𝓥^C 𝓒^C} {𝓥^R‿BC : RModel 𝓥^B 𝓥^C ℓ^REB} {𝓥^R : {Θ Δ Γ : Cx Ty} (ρ^A : (Γ -Env) 𝓥^A Δ) (ρ^B : (Δ -Env) 𝓥^B Θ) (ρ^C : (Γ -Env) 𝓥^C Θ) → Set ℓ^RE} {𝓒^R : RModel 𝓒^B 𝓒^C ℓ^RM} (fusable : Fusable 𝓢^A 𝓢^B 𝓢^C 𝓥^R‿BC 𝓥^R 𝓒^R) where
  open Fusable fusable

  lemma :  {Γ Δ Θ : Cx Ty} {σ : Ty} (t : Tm σ Γ) {ρ^A : (Γ -Env) 𝓥^A Δ} {ρ^B : (Δ -Env) 𝓥^B Θ} {ρ^C : (Γ -Env) 𝓥^C Θ} (ρ^R : 𝓥^R ρ^A ρ^B ρ^C) →
           𝓡 t ρ^A ρ^B ρ^C
  lemma (`var v)       ρ^R = R⟦var⟧ v ρ^R
  lemma (f `$ t)       ρ^R = R⟦$⟧ f t (lemma f ρ^R) (lemma t ρ^R) ρ^R
  lemma (`λ t)         ρ^R = R⟦λ⟧ t (λ inc u^R → lemma t (𝓥^R‿∙ (𝓥^R‿th inc ρ^R) u^R)) ρ^R
  lemma `⟨⟩            ρ^R = R⟦⟨⟩⟧ ρ^R
  lemma `tt            ρ^R = R⟦tt⟧ ρ^R
  lemma `ff            ρ^R = R⟦ff⟧ ρ^R
  lemma (`if b l r)  ρ^R = R⟦if⟧ b l r ρ^R (lemma b ρ^R) (lemma l ρ^R) (lemma r ρ^R)
\end{code}}

\paragraph{The Special Case of Syntactic Semantics}

The translation from \AR{Syntactic} to \AR{Semantics} uses a lot
of constructors as their own semantic counterpart, it is hence possible to generate
evidence of \AR{Syntactic} triplets being fusable with much fewer assumptions.
We isolate them and prove the result generically to avoid repetition. A
\AR{SyntacticFusable} record packs the evidence for
\AR{Syntactic} semantics \AB{syn^A}, \AB{syn^B} and \AB{syn^C}. It is indexed
by these three \AR{Syntactic}s as well as two relations corresponding to the
\AB{𝓥^R_{BC}} and \AB{𝓥^R} ones of the \AR{Fusable} framework.
It contains the same \ARF{𝓥^R‿∙}, \ARF{𝓥^R‿th} and \ARF{R⟦var⟧}
fields as a \AR{Fusable} as well as a fourth one (\ARF{var‿0^{BC}})
saying that \AB{syn^B} and \AB{syn^C}'s respective \ARF{var‿0}s are
producing related values.
\AgdaHide{
\begin{code}
record SyntacticFusable
  {ℓ^EA ℓ^EB ℓ^EC ℓ^REBC ℓ^RE : Level} {𝓥^A : Model ℓ^EA} {𝓥^B : Model ℓ^EB} {𝓥^C : Model ℓ^EC} (synA : Syntactic 𝓥^A)
  (synB : Syntactic 𝓥^B)
  (synC : Syntactic 𝓥^C)
  (𝓥^R‿BC : RModel 𝓥^B 𝓥^C ℓ^REBC)
  (𝓥^R : {Θ Δ Γ : Cx Ty} (ρ^A : (Γ -Env) 𝓥^A Δ) (ρ^B : (Δ -Env) 𝓥^B Θ) (ρ^C : (Γ -Env) 𝓥^C Θ) → Set ℓ^RE)
  : Set (ℓ^RE ⊔ ℓ^REBC ⊔ ℓ^EC ⊔ ℓ^EB ⊔ ℓ^EA)
  where
  module Syn^A = Syntactic synA
  module Syn^B = Syntactic synB
  module Syn^C = Syntactic synC
  field
    𝓥^R‿∙ : ({Γ Δ Θ : Cx Ty} {σ : Ty} {ρ^A : (Γ -Env) 𝓥^A Δ} {ρ^B : (Δ -Env) 𝓥^B Θ} {ρ^C : (Γ -Env) 𝓥^C Θ}
               {u^B : 𝓥^B σ Θ} {u^C : 𝓥^C σ Θ} (ρ^R : 𝓥^R ρ^A ρ^B ρ^C) (u^R : rmodel 𝓥^R‿BC u^B u^C) →
               𝓥^R (th[ Syn^A.th ] (step refl) ρ^A `∙ Syn^A.var‿0)
                      (ρ^B `∙ u^B)
                      (ρ^C `∙ u^C))
    𝓥^R‿th : {Γ Δ Θ E : Cx Ty} (inc : Θ ⊆ E)
               {ρ^A : (Γ -Env) 𝓥^A Δ} {ρ^B : (Δ -Env) 𝓥^B Θ} {ρ^C : (Γ -Env) 𝓥^C Θ} (ρ^R : 𝓥^R ρ^A ρ^B ρ^C) →
               𝓥^R ρ^A(th[ Syn^B.th ] inc ρ^B) (th[ Syn^C.th ] inc ρ^C)
    R⟦var⟧  : {Γ Δ Θ : Cx Ty} {σ : Ty} {ρ^A : (Γ -Env) 𝓥^A Δ} {ρ^B : (Δ -Env) 𝓥^B Θ} {ρ^C : (Γ -Env) 𝓥^C Θ}
              → (v : Var σ Γ) → 𝓥^R ρ^A ρ^B ρ^C →
              Eval.sem (syntactic synB) ρ^B (Eval.sem (syntactic synA) ρ^A (`var v))
              ≡ Eval.sem (syntactic synC) ρ^C (`var v)
\end{code}}
\begin{code}
    var‿0^BC : {Γ : Cx Ty} {σ : Ty} → rmodel 𝓥^R‿BC {σ} {Γ ∙ σ} Syn^B.var‿0 Syn^C.var‿0
\end{code}

\begin{theorem}[Fundamental Lemma of Fusable Syntactics]
Given a \AR{SyntacticFusable} relating three \AR{Syntactic} semantics,
we get a \AR{Fusable} relating the corresponding \AR{Semantics} where
\AB{𝓒^R} is the propositional equality.
\end{theorem}
\begin{proof}The proof relies on the way the translation from \AR{Syntactic}
to \AR{Semantics} is formulated in \cref{syntactic}.
\end{proof}
\AgdaHide{
\begin{code}
syntacticFusable :  {ℓ^EA ℓ^EB ℓ^EC ℓ^RE ℓ^REBC : Level} {𝓥^A : Model ℓ^EA} {𝓥^B : Model ℓ^EB} {𝓥^C : Model ℓ^EC} {syn^A : Syntactic 𝓥^A} {syn^B : Syntactic 𝓥^B} {syn^C : Syntactic 𝓥^C} {𝓥^R‿BC : RModel 𝓥^B 𝓥^C ℓ^REBC} {𝓥^R : {Θ Δ Γ : Cx Ty} (ρ^A : (Γ -Env) 𝓥^A Δ) (ρ^B : (Δ -Env) 𝓥^B Θ) (ρ^C : (Γ -Env) 𝓥^C Θ) → Set ℓ^RE} (syn^R : SyntacticFusable syn^A syn^B syn^C 𝓥^R‿BC 𝓥^R) →
  Fusable (syntactic syn^A) (syntactic syn^B) (syntactic syn^C) 𝓥^R‿BC 𝓥^R PropEq
syntacticFusable synF =
  let open SyntacticFusable synF in
  record
    { reify^A    = id
    ; 𝓥^R‿∙   = 𝓥^R‿∙
    ; 𝓥^R‿th  = 𝓥^R‿th
    ; R⟦var⟧    = R⟦var⟧
    ; R⟦$⟧      = λ f t eqf eqt ρ^R → PEq.cong₂ _`$_ eqf eqt
    ; R⟦λ⟧      = λ t r ρ^R → PEq.cong `λ (r (step refl) var‿0^BC)
    ; R⟦⟨⟩⟧     = λ ρ^R → PEq.refl
    ; R⟦tt⟧     = λ ρ^R → PEq.refl
    ; R⟦ff⟧     = λ ρ^R → PEq.refl
    ; R⟦if⟧   = λ b l r ρ^R eqb eql → PEq.cong₂ (uncurry `if) (PEq.cong₂ _,_ eqb eql)
    }

`var-inj : {Γ : Cx Ty} {σ : Ty} {pr₁ pr₂ : Var σ Γ} (eq : (Tm σ Γ F.∋ `var pr₁) ≡ `var pr₂) → pr₁ ≡ pr₂
`var-inj PEq.refl = PEq.refl
\end{code}}

\begin{corollary}[Renaming-Renaming fusion]Given two renamings \AB{ρ} from
\AB{Γ} to \AB{Δ} and \AB{ρ′} from \AB{Δ} to \AB{Θ} and a term \AB{t} of type
\AB{σ} with free variables in \AB{Γ}, we have that:
\AgdaHide{
\begin{code}
RenamingFusable :
  SyntacticFusable  syntacticRenaming syntacticRenaming syntacticRenaming
                    PropEq (λ ρ^A ρ^B ρ^C → ∀ σ pr → lookup (select ρ^A ρ^B) pr ≡ lookup ρ^C pr)
RenamingFusable = record
  { 𝓥^R‿∙     = λ ρ^R eq → [ eq ,, ρ^R ]
  ; 𝓥^R‿th    = λ inc ρ^R σ pr → PEq.cong (lookup inc) (ρ^R σ pr)
  ; R⟦var⟧    = λ v ρ^R → PEq.cong `var (ρ^R _ v)
  ; var‿0^BC  = PEq.refl }

ren-ren : {Γ Δ Θ : Cx Ty} {σ : Ty} (ρ : Γ ⊆ Δ) (ρ′ : Δ ⊆ Θ) (t : Tm σ Γ) → 
\end{code}}
\begin{code}
 th^Tm σ ρ′ (th^Tm σ ρ t) ≡ th^Tm σ (select ρ ρ′) t
\end{code}
\AgdaHide{
\begin{code}
ren-ren ρ ρ′ t = let open Fusion (syntacticFusable RenamingFusable) in lemma t (λ _ _ → PEq.refl)
\end{code}}
\end{corollary}

\begin{corollary}[Renaming-Substitution fusion]Given a renaming \AB{ρ} from
\AB{Γ} to \AB{Δ}, a substitution \AB{ρ′} from \AB{Δ} to \AB{Θ} and a term
\AB{t} of type \AB{σ} with free variables in \AB{Γ}, we have that:\vspace*{ -1.5em}
\AgdaHide{
\begin{code}
RenamingSubstitutionFusable :
  SyntacticFusable syntacticRenaming syntacticSubstitution syntacticSubstitution
  PropEq (λ ρ^A ρ^B ρ^C → ∀ σ pr → lookup ρ^B (lookup ρ^A pr) ≡ lookup ρ^C pr)
RenamingSubstitutionFusable = record
  { 𝓥^R‿∙   = λ ρ^R eq → [ eq ,, ρ^R ]
  ; 𝓥^R‿th  = λ inc ρ^R σ pr → PEq.cong (th^Tm σ inc) (ρ^R σ pr)
  ; R⟦var⟧    = λ v ρ^R → ρ^R _ v
  ; var‿0^BC   = PEq.refl }

ren-sub : {Γ Δ Θ : Cx Ty} {σ : Ty} (ρ : Γ ⊆ Δ) (ρ′ : (Δ -Env) Tm Θ) (t : Tm σ Γ) → 
\end{code}}
\begin{code}
 subst ρ′ (th^Tm σ ρ t) ≡ subst (select ρ ρ′) t
\end{code}
\AgdaHide{
\begin{code}
ren-sub ρ ρ′ t = let open Fusion (syntacticFusable RenamingSubstitutionFusable) in lemma t (λ _ _ → PEq.refl)
\end{code}}
\end{corollary}

\begin{corollary}[Substitution-Renaming fusion]Given a substitution \AB{ρ}
from \AB{Γ} to \AB{Δ}, a renaming \AB{ρ′} from \AB{Δ} to \AB{Θ} and a term
\AB{t} of type \AB{σ} with free variables in \AB{Γ}, we have that:\vspace*{ -1.5em}
\AgdaHide{
\begin{code}
SubstitutionRenamingFusable :
  SyntacticFusable syntacticSubstitution syntacticRenaming syntacticSubstitution
  (mkRModel (_≡_ ∘ `var)) (λ ρ^A ρ^B ρ^C → ∀ σ pr → th^Tm σ ρ^B (lookup ρ^A pr) ≡ lookup ρ^C pr)
SubstitutionRenamingFusable =
  let module RenRen = Fusion (syntacticFusable RenamingFusable) in
  record { 𝓥^R‿∙   = λ {_} {_} {_} {_} {ρ^A} {ρ^B} {ρ^C} ρ^R eq → [ eq ,, (λ σ pr →
                         PEq.trans (RenRen.lemma (lookup ρ^A pr) (λ _ _ → PEq.refl))
                                   (ρ^R σ pr)) ]
         ; 𝓥^R‿th  = λ inc {ρ^A} {ρ^B} {ρ^C} ρ^R σ pr →
                         PEq.trans (PEq.sym (RenRen.lemma (lookup ρ^A pr) (λ _ _ → PEq.refl)))
                                   (PEq.cong (th^Tm σ inc) (ρ^R σ pr))
         ; R⟦var⟧    = λ v ρ^R → ρ^R _ v
         ; var‿0^BC   = PEq.refl }
sub-ren : {Γ Δ Θ : Cx Ty} {σ : Ty} (ρ : (Γ -Env) Tm Δ) (ρ′ : Δ ⊆ Θ) (t : Tm σ Γ) → 
\end{code}}
\begin{code}
 th^Tm σ ρ′ (subst ρ t) ≡ subst (map^Env (th^Tm _ ρ′) ρ) t
\end{code}
\AgdaHide{
\begin{code}
sub-ren ρ ρ′ t = let open Fusion (syntacticFusable SubstitutionRenamingFusable) in lemma t (λ _ _ → PEq.refl)
\end{code}}
\end{corollary}

\begin{corollary}[Substitution-Substitution fusion]Given two substitutitons,
\AB{ρ} from \AB{Γ} to \AB{Δ} and \AB{ρ′} from \AB{Δ} to \AB{Θ}, and a term
\AB{t} of type \AB{σ} with free variables in \AB{Γ}, we have that:\vspace*{ -1.5em}
\AgdaHide{
\begin{code}
SubstitutionFusable :
  SyntacticFusable syntacticSubstitution syntacticSubstitution syntacticSubstitution
  PropEq (λ ρ^A ρ^B ρ^C → ∀ σ pr → subst ρ^B (lookup ρ^A pr) ≡ lookup ρ^C pr)
SubstitutionFusable =
  let module RenSubst = Fusion (syntacticFusable RenamingSubstitutionFusable)
      module SubstRen = Fusion (syntacticFusable SubstitutionRenamingFusable) in
  record { 𝓥^R‿∙   = λ {_} {_} {_} {_} {ρ^A} {ρ^B} {ρ^C} ρ^R eq → [ eq ,, (λ σ pr →
                         PEq.trans (RenSubst.lemma (lookup ρ^A pr) (λ _ _ → PEq.refl))
                                   (ρ^R σ pr)) ]
         ; 𝓥^R‿th  = λ inc {ρ^A} {ρ^B} {ρ^C} ρ^R σ pr →
                         PEq.trans (PEq.sym (SubstRen.lemma (lookup ρ^A pr) (λ _ _ → PEq.refl)))
                                   (PEq.cong (th^Tm σ inc) (ρ^R σ pr))
         ; R⟦var⟧    = λ v ρ^R → ρ^R _ v
         ; var‿0^BC   = PEq.refl }

ifRenNorm :
      {Γ Δ Θ : Cx Ty} {σ : Ty} (b : Tm `2 Γ) (l r : Tm σ Γ)
      {ρ^A : Γ ⊆ Δ} {ρ^B : (Δ -Env) Kr Θ}
      {ρ^C : (Γ -Env) Kr Θ} →
      (ρ^R : (σ : Ty) (pr : Var σ Γ) → PER σ (lookup ρ^B (lookup ρ^A pr)) (lookup ρ^C pr)) →
      Eval.sem Normalise ρ^B (th^Tm `2 ρ^A b) ≡ Eval.sem Normalise ρ^C b →
      PER σ (Eval.sem Normalise ρ^B (th^Tm σ ρ^A l)) (Eval.sem Normalise ρ^C l) →
      PER σ (Eval.sem Normalise ρ^B (th^Tm σ ρ^A r)) (Eval.sem Normalise ρ^C r) →
      PER σ (Eval.sem Normalise ρ^B (th^Tm σ ρ^A (`if b l r))) (Eval.sem Normalise ρ^C (`if b l r))
ifRenNorm b l r {ρ^A} {ρ^B} {ρ^C} ρ^R eqb eql eqr
  with Eval.sem Normalise  ρ^B (th^Tm _ ρ^A b)
     | Eval.sem Normalise ρ^C b
ifRenNorm b l r ρ^R PEq.refl eql eqr | `ne _ t | `ne _ .t =
  reflect^PER _ (PEq.cong₂ (uncurry `if) (PEq.cong₂ _,_ PEq.refl (reify^PER _ eql)) (reify^PER _ eqr))
ifRenNorm b l r ρ^R () eql eqr | `ne _ t | `tt
ifRenNorm b l r ρ^R () eql eqr | `ne _ t | `ff
ifRenNorm b l r ρ^R () eql eqr | `tt | `ne _ t
ifRenNorm b l r ρ^R PEq.refl eql eqr | `tt | `tt = eql
ifRenNorm b l r ρ^R () eql eqr | `tt | `ff
ifRenNorm b l r ρ^R () eql eqr | `ff | `ne _ t
ifRenNorm b l r ρ^R () eql eqr | `ff | `tt
ifRenNorm b l r ρ^R PEq.refl eql eqr | `ff | `ff = eqr
sub-sub : {Γ Δ Θ : Cx Ty} {σ : Ty} (ρ : (Γ -Env) Tm Δ) (ρ′ : (Δ -Env) Tm Θ) (t : Tm σ Γ) → 
\end{code}}
\begin{code}
 subst ρ′ (subst ρ t) ≡ subst (map^Env (subst ρ′) ρ) t
\end{code}
\AgdaHide{
\begin{code}
sub-sub ρ ρ′ t = let open Fusion (syntacticFusable SubstitutionFusable) in lemma t (λ _ _ → PEq.refl)
\end{code}}
\end{corollary}

These four lemmas are usually proven in painful separation. Here
we discharged them by rapid successive instantiation of our framework,
using the earlier results to satisfy the later constraints.
We are not limited to \AR{Syntactic} statements:

\paragraph{Examples of Fusable Semantics}

The most simple example of \AR{Fusable} \AR{Semantics} involving a non
\AR{Syntactic} one is probably the proof that \AR{Renaming} followed
by \AR{Normalise^{βιξη}} is equivalent to NBE with an adjusted environment.

\begin{corollary}[Renaming-Normalise fusion] Given a renaming \AB{ρ}
from \AB{Γ} to \AB{Δ}, an environment of values \AB{ρ′} from \AB{Δ} to
\AB{Θ} such that they are all equal to themselves in the \AF{PER} and
a term \AB{t} of type \AB{σ} with free variables in \AB{Γ}, we have that:\vspace*{ -1.5em}
\AgdaHide{
\begin{code}
RenamingNormaliseFusable : Fusable Renaming Normalise Normalise PER′
  (λ ρ^A ρ^B ρ^C → ∀ σ pr → PER σ (lookup ρ^B (lookup ρ^A pr)) (lookup ρ^C pr)) PER′
RenamingNormaliseFusable =
  record
    { reify^A   = id
    ; 𝓥^R‿∙  = λ ρ^R u^R → [ u^R ,, ρ^R ]
    ; 𝓥^R‿th = λ inc ρ^R → λ σ pr → th^PER σ inc (ρ^R σ pr)
    ; R⟦var⟧   = λ v ρ^R → ρ^R _ v
    ; R⟦$⟧     = λ _ _ r eq _ → r refl eq
    ; R⟦λ⟧     = λ _ r _ inc eq → r inc eq
    ; R⟦⟨⟩⟧    = λ _ → ⟨⟩
    ; R⟦tt⟧    = λ _ → PEq.refl
    ; R⟦ff⟧    = λ _ → PEq.refl
    ; R⟦if⟧  = ifRenNorm
    }

ren-nbe : {Γ Δ Θ : Cx Ty} {σ : Ty} (ρ : Γ ⊆ Δ) (ρ′ : (Δ -Env) Kr Θ) (t : Tm σ Γ) (ρ^R : `∀[ PER′ ] ρ′ ρ′) →
\end{code}}
\begin{code}
 PER σ (nbe ρ′ (th^Tm σ ρ t)) (nbe (select ρ ρ′) t)
\end{code}
\AgdaHide{
\begin{code}
ren-nbe ρ ρ′ t ρ^R = let open Fusion RenamingNormaliseFusable
                     in lemma t (λ σ pr → lookup^R ρ^R (lookup ρ pr))
\end{code}}
\end{corollary}

\AgdaHide{
\begin{code}
ifSubstNorm :
     {Γ Δ Θ : Cx Ty} {σ : Ty} (b : Tm `2 Γ) (l r : Tm σ Γ)
      {ρ^A : (Γ -Env) Tm Δ} {ρ^B : (Δ -Env) Kr Θ}
      {ρ^C : (Γ -Env) Kr Θ} →
      (`∀[ PER′ ] ρ^B ρ^B) ×
      ((σ₁ : Ty) (pr : Var σ₁ Γ) {Θ₁ : Cx Ty} (inc : Θ ⊆ Θ₁) →
       PER σ₁
       (Eval.sem Normalise (pack (λ {σ} → th^Kr σ inc ∘ lookup ρ^B)) (lookup ρ^A pr))
       (th^Kr σ₁ inc (lookup ρ^C pr)))
      ×
      ((σ₁ : Ty) (pr : Var σ₁ Γ) →
       PER σ₁ (Eval.sem Normalise ρ^B (lookup ρ^A  pr)) (lookup ρ^C pr)) →
      Eval.sem Normalise ρ^B (subst ρ^A b) ≡ Eval.sem Normalise ρ^C b →
      PER σ (Eval.sem Normalise ρ^B (subst ρ^A l)) (Eval.sem Normalise ρ^C l) →
      PER σ (Eval.sem Normalise ρ^B (subst ρ^A r)) (Eval.sem Normalise ρ^C r) →
      PER σ (Eval.sem Normalise ρ^B (subst ρ^A (`if b l r))) (Eval.sem Normalise ρ^C (`if b l r))
ifSubstNorm b l r {ρ^A} {ρ^B} {ρ^C} ρ^R eqb eql eqr
  with Eval.sem Normalise ρ^B (subst ρ^A b)
     | Eval.sem Normalise ρ^C b
ifSubstNorm b l r ρ^R PEq.refl eql eqr | `ne _ t | `ne _ .t =
  reflect^PER _ (PEq.cong₂ (uncurry `if) (PEq.cong₂ _,_ PEq.refl (reify^PER _ eql)) (reify^PER _ eqr))
ifSubstNorm b l r ρ^R () eql eqr | `ne _ t | `tt
ifSubstNorm b l r ρ^R () eql eqr | `ne _ t | `ff
ifSubstNorm b l r ρ^R () eql eqr | `tt | `ne _ t
ifSubstNorm b l r ρ^R PEq.refl eql eqr | `tt | `tt = eql
ifSubstNorm b l r ρ^R () eql eqr | `tt | `ff
ifSubstNorm b l r ρ^R () eql eqr | `ff | `ne _ t
ifSubstNorm b l r ρ^R () eql eqr | `ff | `tt
ifSubstNorm b l r ρ^R PEq.refl eql eqr | `ff | `ff = eqr

th-refl : {Γ : Cx Ty} (σ : Ty) {T U : Kr σ Γ} →
          PER σ T U → PER σ (th^Kr σ refl T) U
th-refl `1     eq = ⟨⟩
th-refl `2     eq = PEq.trans (th^nf-refl _) eq
th-refl (σ `→ τ)  eq = eq

th^2 : {Θ Δ Γ : Cx Ty} (σ : Ty) (inc₁ : Γ ⊆ Δ) (inc₂ : Δ ⊆ Θ) {T U : Kr σ Γ} →
       PER σ T U → PER σ (th^Kr σ inc₂ (th^Kr σ inc₁ T)) (th^Kr σ (select inc₁ inc₂) U)
th^2 `1     inc₁ inc₂ eq = ⟨⟩
th^2 `2     inc₁ inc₂ eq = PEq.trans (th^nf-trans inc₁ inc₂ _) (PEq.cong (th^nf `2 (select inc₁ inc₂)) eq)
th^2 (σ `→ τ)  inc₁ inc₂ eq = λ inc₃ → eq (select inc₁ (select inc₂ inc₃))
\end{code}}

Then, we use the framework to prove that to \AR{Normalise^{βιξη}} by
Evaluation after a \AR{Substitution} amounts to normalising the original
term where the substitution has been evaluated first. The constraints
imposed on the environments might seem quite restrictive but they are
actually similar to the Uniformity condition described by C. Coquand~(\citeyear{coquand2002formalised})
in her detailed account of NBE for a ST$λ$C with explicit substitution.


\begin{corollary}[Substitution-Normalise fusion]Given a substitution \AB{ρ}
from \AB{Γ} to \AB{Δ}, an environment of values \AB{ρ′} from \AB{Δ} to \AB{Θ}
such that all these values are equal to themselves and thinning and evaluation
in \AB{ρ′} commute, and a term \AB{t} of type \AB{σ} with free variables in \AB{Γ},
we have that:
\AgdaHide{
\begin{code}
SubstitutionNormaliseFusable : Fusable  Substitution Normalise Normalise
  PER′
  (λ ρ^A ρ^B ρ^C → `∀[ PER′ ] ρ^B ρ^B
                 × ((σ : Ty) (pr : Var σ _) {Θ : Cx Ty} (inc : _ ⊆ Θ) →
                      PER σ (Eval.sem Normalise (pack (λ {σ} pr → th^Kr σ inc (lookup ρ^B pr))) (lookup ρ^A pr)) (th^Kr σ inc (lookup ρ^C pr)))
                 × ((σ : Ty) (pr : Var σ _) → PER σ (Eval.sem Normalise ρ^B (lookup ρ^A pr)) (lookup ρ^C pr)))
  PER′
SubstitutionNormaliseFusable =
  let module RenNorm = Fusion RenamingNormaliseFusable
      module EqNorm  = Simulate SimulationNormalise in
  record
    { reify^A   = id
    ; 𝓥^R‿∙  = λ {_} {_} {_} {_} {ρ^A} {ρ^B} {ρ^C} ρ^R u^R →
                     (proj₁ ρ^R ∙^R refl^PER _ u^R)
                   , [ (λ {Θ} inc → th^PER _ inc u^R)
                     ,, (λ σ pr {Θ} inc →
                       trans^PER σ (RenNorm.lemma (lookup ρ^A pr)
                                                    (λ σ pr → th^PER σ inc (lookup^R (proj₁ ρ^R) pr)))
                                    ((proj₁ ∘ proj₂) ρ^R σ pr inc)) ]
                     , [ u^R ,, (λ σ pr → trans^PER σ (RenNorm.lemma (lookup ρ^A pr) (λ _ → lookup^R (proj₁ ρ^R)))
                                          ((proj₂ ∘ proj₂) ρ^R σ pr)) ]
    ; 𝓥^R‿th = λ inc {ρ^A} ρ^R → pack^R (λ pr → th^PER _ inc (lookup^R (proj₁ ρ^R) pr))
                          , (λ σ pr inc′ →
       trans^PER σ (EqNorm.sim (lookup ρ^A pr) (pack^R (λ {τ} v → trans^PER τ (th^2 τ inc inc′ (lookup^R (proj₁ ρ^R) v)) (th^PER τ (select inc inc′) (lookup^R (proj₁ ρ^R) v)))))
       (trans^PER σ ((proj₁ (proj₂ ρ^R)) σ pr (select inc inc′))
       (sym^PER σ (th^2 σ inc inc′ (refl^PER σ (sym^PER σ (proj₂ (proj₂ ρ^R) σ pr)))))))
                          , (λ σ pr → (proj₁ ∘ proj₂) ρ^R σ pr inc)
    ; R⟦var⟧   = λ v ρ^R → (proj₂ ∘ proj₂) ρ^R _ v
    ; R⟦$⟧     = λ _ _ r eq _ → r refl eq
    ; R⟦λ⟧     = λ _ r _ inc eq → r inc eq
    ; R⟦⟨⟩⟧    = λ _ → ⟨⟩
    ; R⟦tt⟧    = λ _ → PEq.refl
    ; R⟦ff⟧    = λ _ → PEq.refl
    ; R⟦if⟧  = ifSubstNorm
    }

both : {A B : Set} {a₁ a₂ : A} {b₁ b₂ : B} (eq : (A × B F.∋ a₁ , b₁) ≡ (a₂ , b₂)) → a₁ ≡ a₂ × b₁ ≡ b₂
both PEq.refl = PEq.refl , PEq.refl

∷-inj : {A : Set} {a b : A} {as bs : ∞ (Stream A)} (eq : (Stream A F.∋ a ∷ as) ≡ b ∷ bs) → a ≡ b × as ≡ bs
∷-inj PEq.refl = PEq.refl , PEq.refl

sub-nbe : {Γ Δ Θ : Cx Ty} {σ : Ty} (ρ : (Γ -Env) Tm Δ) (ρ′ : (Δ -Env) Kr Θ) (t : Tm σ Γ) (ρ^R : `∀[ PER′ ] ρ′ ρ′) → ∀ ρ^R′ →
\end{code}}
\begin{code}
 PER σ (nbe ρ′ (subst ρ t)) (nbe (map^Env (nbe ρ′) ρ) t)
\end{code}
\AgdaHide{
\begin{code}
sub-nbe ρ ρ′ t ρ^R ρ^R′ =
  let open Fusion SubstitutionNormaliseFusable
  in lemma t
     (ρ^R
     , ρ^R′
     , (λ σ pr → let open Simulate SimulationNormalise in sim (lookup ρ pr) ρ^R))
\end{code}}
\end{corollary}


%Finally, we use \AR{Fusable} to prove that our
%definition of pretty-printing ignores \AR{Renamings}. In other
%words, as long as the names provided for the free variables are
%compatible after the renaming and as long as the name supplies
%are equal then the string produced, as well as the state of the
%name supply at the end of the process, are equal.

%\begin{corollary}[Renaming-Printing fusion]
\AgdaHide{
\begin{code}
RenamingPrettyPrintingFusable : Fusable Renaming Printing Printing PropEq
  (λ ρ^A ρ^B → `∀[ PropEq ] (select ρ^A ρ^B))
  (mkRModel (λ p q → ∀ {names₁ names₂} → names₁ ≡ names₂ → runP p names₁ ≡ runP q names₂))
RenamingPrettyPrintingFusable = record
  { reify^A   = id
  ; 𝓥^R‿∙   = λ {Γ} {Δ} {Θ} {σ} {ρ^A} {ρ^B} {ρ^C} {u^B} {u^C} ρ^R eq → pack^R ((λ {σ} v → [_,,_] {P = λ σ v → lookup (select (step ρ^A `∙ ze) (ρ^B `∙ u^B)) v ≡ lookup (ρ^C `∙ u^C) v} eq (λ σ v → lookup^R ρ^R v) σ v))
  ; 𝓥^R‿th  = λ _ ρ^R → pack^R (PEq.cong (mkN ∘ getN) ∘ lookup^R ρ^R)
  ; R⟦var⟧   = λ v ρ^R → PEq.cong₂ (λ n ns → getN n , ns) (lookup^R ρ^R v)
  ; R⟦λ⟧     = λ t r ρ^R → λ { {n₁ ∷ n₁s} {n₂ ∷ n₂s} eq →
                        let (neq   , nseq) = ∷-inj eq
                            (ihstr , ihns) = both (r (step refl) (PEq.cong mkN neq) (PEq.cong ♭ nseq))
                        in PEq.cong₂ _,_ (PEq.cong₂ (λ n str → "λ" ++ n ++ ". " ++ str) neq ihstr) ihns }
  ; R⟦$⟧     = λ f t {ρ^A} {ρ^B} {ρ^C} ihf iht ρ^R eq →
                        let (ihstrf , eq₁) = both (ihf eq)
                            (ihstrt , eq₂) = both (iht eq₁)
                        in PEq.cong₂ _,_ (PEq.cong₂ (λ strf strt → strf ++ " (" ++ strt ++ ")") ihstrf ihstrt) eq₂
  ; R⟦⟨⟩⟧    = λ _ → PEq.cong _
  ; R⟦tt⟧    = λ _ → PEq.cong _
  ; R⟦ff⟧    = λ _ → PEq.cong _
  ; R⟦if⟧    = λ b l r {ρ^A} {ρ^B} {ρ^C} ρ^R ihb ihl ihr eq →
                       let (ihstrb , eq₁) = both (ihb eq)
                           (ihstrl , eq₂) = both (ihl eq₁)
                           (ihstrr , eq₃) = both (ihr eq₂)
                       in PEq.cong₂ _,_ (PEq.cong₂ (λ strb strlr → "if (" ++ strb ++ ") then (" ++ strlr)
                                        ihstrb (PEq.cong₂ (λ strl strr → strl ++ ") else (" ++ strr ++ ")")
                                        ihstrl ihstrr)) eq₃ }

tailComm : (Δ Γ : Cx Ty) {names : Stream String} →
           tail (proj₂ (nameContext Δ Γ names)) ≡ proj₂ (nameContext Δ Γ (tail names))
tailComm Δ ε        = PEq.refl
tailComm Δ (Γ ∙ _)  = PEq.cong tail (tailComm Δ Γ)

proof : (Δ Γ : Cx Ty) {names : Stream String} → proj₂ (nameContext Δ Γ names) ≡ Stream.drop (size Γ) names
proof Δ ε                = PEq.refl
proof Δ (Γ ∙ x) {n ∷ ns} = PEq.trans (tailComm Δ Γ) (proof Δ Γ)

ren-print : {Γ : Cx Ty} {σ : Ty} (t : Tm σ ε) (inc : ε ⊆ Γ) →
\end{code}
\begin{code}
 print (th^Tm σ inc t) ≡ proj₁ (runP (Eval.sem Printing `ε t) (Stream.drop (size Γ) names))
\end{code}
\begin{code}
ren-print {Γ} t inc = PEq.cong proj₁ (lemma t (pack^R (λ ())) (proof Γ Γ))
  where open Fusion RenamingPrettyPrintingFusable
\end{code}}
%\end{corollary}


\section{Future and Related Work}

The programming part of this work can be replicated in Haskell and a translation
of the definitions is available in the paper's
repository~\cite{repo}
The subtleties of working with dependent types in Haskell~\cite{lindley2014hasochism}
are outside the scope of this paper.

If the Tagless and Typeful NbE procedure derived in Haskell from our Semantics
framework is to the best of our knowledge the first of its kind, Danvy,
Keller and Puech have achieved a similar goal in OCaml~(\citeyear{danvytagless}).
But their formalisation uses parametric higher order abstract syntax~\cite{chlipala2008parametric}
freeing them from having to deal with variable binding, contexts and use models à
la Kripke at the cost of using a large encoding. However we find scope safety
enforced at the type level to be a helpful guide when formalising complex
type theories. It helps us root out bugs related to fresh name generation,
name capture or conversion from de Bruijn levels to de Bruijns indices.

This paper's method really shines in a simply typed setting but it is not
limited to it: we have successfully used an analogue of our Semantics
framework to enforce scope safety when implementing the expected traversals
(renaming, substitution, untyped normalisation by evaluation and printing
with names) for the untyped λ-calculus (for which the notion of type safety
does not make sense) or Martin-Löf type theory. Apart from NbE (which relies
on a non strictly-positive datatype), all of these traversals are total.
Simulation and Fusion fundamental theorems akin to the ones proven in this
paper also hold true. The common structure across all these variations
suggests a possible generic scope safe treatment of syntaxes with binding.

This work is at the intersection of two traditions: the formal treatment
of programming languages and the implementation of embedded Domain Specific
Languages (eDSL)~\cite{hudak1996building} both require the designer to
deal with name binding and the associated notions of renaming and substitution
but also partial evaluation~\cite{danvy1999type}, or even printing when
emitting code or displaying information back to the user~\cite{wiedijk2012pollack}.
The mechanisation of a calculus in a \emph{meta language} can use either
a shallow or a deep embedding~\cite{svenningsson2013combining,gill2014domain}.

The well-scoped and well typed final encoding described by Carette, Kiselyov,
and Shan~(\citeyear{carette2009finally}) allows the mechanisation of a calculus in
Haskell or OCaml by representing terms as expressions built up from the
combinators provided by a ``Symantics''. The correctness of the encoding
relies on parametricity~\cite{reynolds1983types} and although there exists
an ongoing effort to internalise parametricity~\cite{bernardy2013type} in
Type Theory, this puts a formalisation effort out of the reach of all the
current interactive theorem provers.

Because of the strong restrictions on the structure our \AF{Model}s may have,
we cannot represent all the interesting traversals imaginable. Chapman and
Abel's work on normalisation by evaluation~(\citeyear{chapman2009type,abel2014normalization})
which decouples the description of the big-step algorithm and its termination
proof is for instance out of reach for our system. Indeed, in their development
the application combinator may \emph{restart} the computation by calling the
evaluator recursively whereas the \AF{Applicative} constraint we impose means
that we may only combine induction hypotheses.

McBride's original unpublished work~(\citeyear{mcbride2005type}) implemented
in Epigram~\cite{mcbride2004view} was inspired by Goguen and McKinna's
Candidates for Substitution~(\citeyear{goguen1997candidates}). It focuses on
renaming and substitution for the simply typed $λ$-calculus and was later
extended to a formalisation of System F~\cite{girard1972interpretation}
in Coq~\cite{Coq:manual} by Benton, Hur, Kennedy and McBride~(\citeyear{benton2012strongly}).
Benton et al. both implement a denotational semantics for their language
and prove the properties of their traversals. However both of these things
are done in an ad-hoc manner: the meaning function associated to their
denotational semantics is not defined in terms of the generic traversal
and the proofs are manually discharged one by one. They also choose to prove
the evaluation function correct by using propositional equality and assuming
function extensionality rather than resorting to the traditional Partial
Equivalence Relation approach we use.

\section{Conclusion}

We have explained how to make using an inductive family to only represent
the terms of an eDSL which are well-scoped and well typed by construction
more tractable. We proceeded by factoring out a common notion of \AR{Semantics}
encompassing a wide range of type and scope preserving traversals such as
renaming and substitution, which were already handled by the state of the
art, but also pretty printing, or various variations on normalisation by evaluation.
Our approach crucially relied on the careful distinction we made between
values in the environment and values in the model, as well as the slight
variation on the structure typical of Kripke-style models. Indeed, in our
formulation, the domain of a binder's interpretation is an environment
value rather than a model one.

We have then demonstrated that, having this shared structure, one could
further alleviate the implementer's pain by tackling the properties of
these \AR{Semantics} in a similarly abstract approach. We characterised,
using a first logical relation, the traversals which were producing
related outputs provided they were fed related inputs. A more involved
second logical relation gave us a general description of triples of
\AR{Fusable} semantics such that composing the two first ones would
yield an instance of the third one.

\acks
We would like to thank the anonymous
referees for their helpful comments. This work was supported by EPSRC
grant EP/M016951/1 and EP/K020218/1 and the European Research Council
under grant agreement N°320571. Data (Agda code) associated with research
published in this paper is available at the University of Strathclyde's
KnowledgeBase~\cite{repo}.

%\newpage{}
\balance
\bibliographystyle{abbrvnat}
\bibliography{main}

\end{document}
