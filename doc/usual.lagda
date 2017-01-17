\documentclass[xetex, mathserif, serif]{beamer}
\usepackage[utf8]{inputenc}
\usepackage[english]{babel}
\usepackage[references]{agda}
\setmainfont[Ligatures=TeX]{XITS}
\setmathfont{XITS Math}
\usepackage{newunicodechar}
\usepackage{amssymb}

\begin{code}
module usual where

open import models hiding (Semantics ; module Semantics ; Simulation ; module Simulation ; Fusable ; Renaming ; Substitution ; Printing)
open import Data.Unit
open import Data.Bool
open import Function

import Level as L
`Model : Set₁
`Model = Model {Ty} L.zero

`RModel : `Model → `Model → Set₁
`RModel 𝓥 𝓒 = RModel 𝓥 𝓒 L.zero

ren⟦var⟧ : ∀ {σ} → [ Var σ ⟶ Tm σ ]
ren⟦var⟧ = `var

renextend : {Γ Δ : Cx Ty} {σ : Ty} (ρ : (Γ -Env) Var Δ) → (Γ ∙ σ -Env) Var (Δ ∙ σ)
renextend = pop!

\end{code}
%<*rename>
\begin{code}
ren : {Γ Δ : Cx Ty} {σ : Ty} → (Γ -Env) Var Δ → Tm σ Γ → Tm σ Δ
ren ρ (`var v)       = ren⟦var⟧ (lookup ρ v)
ren ρ (t `$ u)       = ren ρ t `$ ren ρ u
ren ρ (`λ t)         = `λ (ren (renextend ρ) t)
\end{code}
%</rename>
\begin{code}
ren ρ `⟨⟩            = `⟨⟩
ren ρ `tt            = `tt
ren ρ `ff            = `ff
ren ρ (`if b l r)  = `if (ren ρ b) (ren ρ l) (ren ρ r)

subextend : {Γ Δ : Cx Ty} {σ : Ty} (ρ : (Γ -Env) Tm Δ) → (Γ ∙ σ -Env) Tm (Δ ∙ σ)
subextend ρ = th[ th^Tm ] (step refl) ρ `∙ `var ze

sub⟦var⟧ = id
\end{code}
%<*subst>
\begin{code}
sub : {Γ Δ : Cx Ty} {σ : Ty} → (Γ -Env) Tm Δ → Tm σ Γ → Tm σ Δ
sub ρ (`var v)        = sub⟦var⟧ (lookup ρ v)
sub ρ (t `$ u)        = sub ρ t  `$ sub ρ u 
sub ρ (`λ t)          = `λ (sub (subextend ρ) t)
\end{code}
%</subst>
\begin{code}
sub ρ `⟨⟩             = `⟨⟩
sub ρ `tt             = `tt
sub ρ `ff             = `ff
sub ρ (`if b l r)   = `if (sub ρ b) (sub ρ l) (sub ρ r)
\end{code}
%<*synextend>
\begin{code}
synextend : ∀ {Γ Δ : Cx Ty} {σ : Ty} {𝓥 : `Model} (𝓢 : Syntactic 𝓥) (ρ : (Γ -Env) 𝓥 Δ) → (Γ ∙ σ -Env) 𝓥 (Δ ∙ σ)
synextend 𝓢 ρ = ρ′ `∙ var
  where  var  = Syntactic.var‿0 𝓢
         ρ′   = pack $ Syntactic.th 𝓢 _ (step refl) ∘ lookup ρ
\end{code}
%</synextend>


%<*syn>
\begin{code}
syn : {Γ Δ : Cx Ty} {σ : Ty} {𝓥 : `Model} (𝓢 : Syntactic 𝓥) → (Γ -Env) 𝓥 Δ → Tm σ Γ → Tm σ Δ
syn 𝓢 ρ (`var v)  = Syntactic.⟦var⟧ 𝓢 (lookup ρ v)
syn 𝓢 ρ (t `$ u)  = syn 𝓢 ρ t `$ syn 𝓢 ρ u
syn 𝓢 ρ (`λ t)    = `λ (syn 𝓢 (synextend 𝓢 ρ) t)
\end{code}
%</syn>
\begin{code}
syn 𝓢 ρ `⟨⟩       = `⟨⟩
syn 𝓢 ρ `tt       = `tt
syn 𝓢 ρ `ff       = `ff
syn 𝓢 ρ (`if b l r)  = `if (syn 𝓢 ρ b) (syn 𝓢 ρ l) (syn 𝓢 ρ r)

sem⟦var⟧ = id

semλ : {Γ Δ Θ : Cx Ty} {σ τ : Ty} (b : Tm τ (Γ ∙ σ)) (⟦t⟧ : (Γ ∙ σ -Env) βιξη.Kr Θ → βιξη.Kr τ Θ)
       (ρ : Δ ⊆ Θ → βιξη.Kr σ Θ → (Γ ∙ σ -Env) βιξη.Kr Θ) (inc : Δ ⊆ Θ) (u : βιξη.Kr σ Θ ) → βιξη.Kr τ Θ
semλ _ ⟦t⟧ ρ inc u = ⟦t⟧ (ρ inc u)

⟨⟩ = tt

semextend : {Γ Δ Θ : Cx Ty} {σ : Ty} (ρ : (Γ -Env) βιξη.Kr Δ) → Δ ⊆ Θ → βιξη.Kr σ Θ → (Γ ∙ σ -Env) βιξη.Kr Θ
semextend ρ inc u = pack (λ {σ} → βιξη.th^Kr σ inc ∘ lookup ρ) `∙ u


sem$ : ∀ {Γ Δ σ τ} → Tm (σ `→ τ) Γ → Tm σ Γ → βιξη.Kr (σ `→ τ) Δ → βιξη.Kr σ Δ → βιξη.Kr τ Δ
sem$ _ _ F T = F refl T

\end{code}

%<*sem>
\begin{code}
sem : {Γ Δ : Cx Ty} {σ : Ty} → (Γ -Env) βιξη.Kr Δ → Tm σ Γ → βιξη.Kr σ Δ
sem ρ (`var v)  = sem⟦var⟧ (lookup ρ v)
sem ρ (t `$ u)  = sem$ t u (sem ρ t) (sem ρ u)
sem ρ (`λ t)    = semλ t (λ ρ → sem ρ t) (semextend ρ)
\end{code}
%</sem>
\begin{code}
sem ρ `⟨⟩             = ⟨⟩
sem ρ `tt             = NormalForms.`tt
sem ρ `ff             = NormalForms.`ff
sem {σ = σ} ρ (`if b l r)   = βιξη.if {σ} (sem ρ b ) (sem ρ l ) (sem ρ r )
\end{code}
%<*semantics>
\begin{code}
record Semantics {ℓ} (𝓔 𝓜 : `Model) : Set ℓ where
  field 
\end{code}\vspace{ -2em}
\uncover<2->{
\begin{code}
    wk      :  ∀ σ → Thinnable (𝓔 σ)
    embed   :  ∀ σ   → [ Var σ ⟶ 𝓔 σ ]
    ⟦var⟧   :  ∀ {σ} → [ 𝓔 σ ⟶ 𝓜 σ ]
\end{code}}\vspace{ -2em}
\uncover<3->{
\begin{code}
    ⟦λ⟧     :  {σ τ : Ty} → [ □ (𝓔 σ ⟶ 𝓜 τ) ⟶ 𝓜 (σ `→ τ) ]
\end{code}}\vspace{ -2em}
\uncover<4->{
\begin{code}
    _⟦$⟧_   :  {σ τ : Ty} → [ 𝓜 (σ `→ τ) ⟶ 𝓜 σ ⟶ 𝓜 τ ]
\end{code}}\vspace{ -2em}
\uncover<5->{
\begin{code}
    ⟦⟨⟩⟧    :  [ 𝓜 `1 ]
    ⟦tt⟧    :  [ 𝓜 `2 ]
    ⟦ff⟧    :  [ 𝓜 `2 ]
    ⟦ifte⟧  :  {σ : Ty} → [ 𝓜 `2 ⟶ 𝓜 σ ⟶ 𝓜 σ ⟶ 𝓜 σ ]
\end{code}}
%</semantics>

%<*semexamples>
\begin{code}
Renaming        : models.Semantics Var Tm
Substitution    : models.Semantics Tm Tm
Printing        : models.Semantics Name Printer
Normalise^βιξη  : models.Semantics βιξη.Kr βιξη.Kr
\end{code}
%</semexamples>

\begin{code}
Renaming = syntactic syntacticRenaming
Substitution = syntactic syntacticSubstitution
Printing = models.Printing
Normalise^βιξη = models.βιξη.Normalise
\end{code}

%<*synchronisable>
\begin{code}
record Synchronisable  {𝓔^A 𝓔^B 𝓜^A 𝓜^B : `Model}
  (𝓢^A : models.Semantics 𝓔^A 𝓜^A) (𝓢^B : models.Semantics 𝓔^B 𝓜^B)
  (𝓔^R  : `RModel 𝓔^A 𝓔^B)
  (𝓜^R  : `RModel 𝓜^A 𝓜^B) : Set where
\end{code}
\AgdaHide{
\begin{code}
  module 𝓢^A = models.Semantics 𝓢^A
  module 𝓢^B = models.Semantics 𝓢^B

  𝓡 : {Γ Δ : Cx Ty} {σ : Ty} → Tm σ Γ → (Γ -Env) 𝓔^A Δ → (Γ -Env) 𝓔^B Δ → Set
  𝓡 t ρ^A ρ^B = rmodel 𝓜^R (Eval.sem 𝓢^A ρ^A t) (Eval.sem 𝓢^B ρ^B t)

  field
\end{code}}\vspace{ -2em}
\uncover<2->{
\begin{code}
    𝓔^R‿wk  :  {Γ Δ Θ : Cx Ty} (inc : Δ ⊆ Θ) {ρ^A : (Γ -Env) 𝓔^A Δ} {ρ^B : (Γ -Env) 𝓔^B Δ} (ρ^R : `∀[ 𝓔^R ] ρ^A ρ^B) →
               `∀[ 𝓔^R ] (th[ 𝓢^A.th ] inc ρ^A) (th[ 𝓢^B.th ] inc ρ^B)
\end{code}}\vspace{ -2em}
\uncover<3->{
\begin{code}
    R⟦var⟧    :  ∀ {Γ Δ σ} (v : Var σ Γ) {ρ^A : (Γ -Env) 𝓔^A Δ} {ρ^B} → `∀[ 𝓔^R ] ρ^A ρ^B → 𝓡 (`var v) ρ^A ρ^B
\end{code}}\vspace{ -2em}
\uncover<4->{
\begin{code}
    R⟦λ⟧ :  ∀ {Γ Δ Θ : Cx Ty} {σ τ} (b : Tm τ (Γ ∙ σ)) {ρ^A : (Γ -Env) 𝓔^A Δ} {ρ^B} →
     (f^R : ∀ {Θ} (pr : Δ ⊆ Θ) {u^A : 𝓔^A σ Θ} {u^B : 𝓔^B σ Θ} (u^R : rmodel 𝓔^R u^A u^B) →
            𝓡 b (th[ 𝓢^A.th ] pr ρ^A `∙ u^A) (th[ 𝓢^B.th ] pr ρ^B `∙ u^B)) →
           `∀[ 𝓔^R ] ρ^A ρ^B →  𝓡 (`λ b) ρ^A ρ^B
\end{code}}
%</synchronisable>
