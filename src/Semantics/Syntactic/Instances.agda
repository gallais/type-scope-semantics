module Semantics.Syntactic.Instances where

open import Syntax.Core
open import Semantics.Environment
open import Semantics.Syntactic.Specification

-- We are, one more, using copatterns to prevent too much unfolding.
SyntacticRenaming : Syntactic _∋_
Syntactic.embed SyntacticRenaming = refl
Syntactic.wk    SyntacticRenaming = wk^∋
Syntactic.⟦var⟧ SyntacticRenaming = `var

𝓢^Renaming = Fundamental.syntactic SyntacticRenaming 

rename : Weakening _⊢_
rename ren t = Fundamental.lemma SyntacticRenaming t ren

SyntacticSubstitution : Syntactic _⊢_
Syntactic.embed SyntacticSubstitution = pack `var
Syntactic.wk    SyntacticSubstitution = rename
Syntactic.⟦var⟧ SyntacticSubstitution = λ t → t

𝓢^Substitution = Fundamental.syntactic SyntacticSubstitution

substitute : {Γ Δ : Context} {σ : Type} → Γ ⊢ σ → Var Γ ⇒[ _⊢_ ] Δ → Δ ⊢ σ
substitute = Fundamental.lemma SyntacticSubstitution
