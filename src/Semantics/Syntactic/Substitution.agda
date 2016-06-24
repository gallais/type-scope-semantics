module Semantics.Syntactic.Substitution where

open import Syntax.Core
open import Semantics.Environment
open import Semantics.Syntactic.Specification
open import Semantics.Syntactic.Renaming

SyntacticSubstitution : Syntactic _⊢_
SyntacticSubstitution = record { embed = pack `var ; wk = rename ; ⟦var⟧ = λ t → t }

𝓢^Substitution = Fundamental.syntactic SyntacticSubstitution

substitute : {Γ Δ : Context} {σ : Type} → Γ ⊢ σ → Var Γ ⇒[ _⊢_ ] Δ → Δ ⊢ σ
substitute = Fundamental.lemma SyntacticSubstitution
