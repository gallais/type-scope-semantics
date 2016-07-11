module Properties.Fusable.Syntactic.Instances where

open import Syntax.Core hiding (_<$>_)
open import Semantics.Environment as Env hiding (refl)
open import Semantics.Syntactic.Instances
open import Properties.Relation
open import Properties.Fusable.Syntactic.Specification

open import Function
open import Relation.Binary.PropositionalEquality hiding (trans)
open ≡-Reasoning

fusableRenaming :
  SyntacticFusable SyntacticRenaming SyntacticRenaming SyntacticRenaming
  Equality (λ ρ^A ρ^B ρ^C → `∀[ Equality ] (trans ρ^A ρ^B) ρ^C)
fusableRenaming = record
  { 𝓔^R‿∙   = λ ρ^R eq → pack^R $ λ { {_} zero → eq ; (1+ v) → lookup^R ρ^R v }
  ; 𝓔^R‿wk  = λ inc ρ^R → pack^R $ cong (lookup inc) ∘ lookup^R ρ^R
  ; R⟦var⟧   = λ v ρ^R → cong `var $ lookup^R ρ^R v
  ; embed^BC = refl
  }

fuseRenamings : ∀ {Γ Δ Θ σ} (t : Γ ⊢ σ) (inc : Renaming Γ Δ) (inc′ : Renaming Δ Θ) →
  rename inc′ (rename inc t) ≡ rename (trans inc inc′) t
fuseRenamings t inc inc′ = Fundamental.lemma fusableRenaming t refl^R

fusableRenamingSubstitution :
  SyntacticFusable SyntacticRenaming SyntacticSubstitution SyntacticSubstitution
  Equality (λ ρ^A ρ^B ρ^C → `∀[ Equality ] (trans ρ^A ρ^B) ρ^C)
fusableRenamingSubstitution = record
  { 𝓔^R‿∙   = λ ρ^R eq → pack^R $ λ { {_} zero → eq ; (1+ v) → lookup^R ρ^R v }
  ; 𝓔^R‿wk  = λ inc ρ^R → pack^R $ cong (rename inc) ∘ lookup^R ρ^R
  ; R⟦var⟧   = λ v ρ^R → lookup^R ρ^R v
  ; embed^BC = refl
  }

fuseRenamingSubstitution :
  ∀ {Γ Δ Θ σ} (t : Γ ⊢ σ) (inc : Renaming Γ Δ) (ρ : Substitution Δ Θ) →
  substitute (rename inc t) ρ ≡ substitute t (trans inc ρ)
fuseRenamingSubstitution t inc ρ = Fundamental.lemma fusableRenamingSubstitution t refl^R

fusableSubstitutionRenaming :
  SyntacticFusable SyntacticSubstitution SyntacticRenaming SyntacticSubstitution
  (mkRModel $ λ v t → `var v ≡ t) (λ ρ^A ρ^B ρ^C → `∀[ Equality ] (rename ρ^B <$> ρ^A) ρ^C)
fusableSubstitutionRenaming = record
  { 𝓔^R‿∙   = λ {_} {_} {_} {_} {ρ^A} {ρ^B} {ρ^C} {u^B} ρ^R eq →
    pack^R $ λ { {_} zero → eq ; (1+ v) →
    begin
      rename (ρ^B `∙ u^B) (rename extend (lookup ρ^A v))
        ≡⟨ fuseRenamings  (lookup ρ^A v) extend (ρ^B `∙ u^B) ⟩
      rename ρ^B (lookup ρ^A v)
        ≡⟨ lookup^R ρ^R v ⟩
      lookup ρ^C v
    ∎ }
  ; 𝓔^R‿wk  = λ inc {ρ^A} {ρ^B} {ρ^C} ρ^R → pack^R $ λ v →
    begin
      rename (trans ρ^B inc) (lookup ρ^A v)
        ≡⟨ sym (fuseRenamings (lookup ρ^A v) ρ^B inc) ⟩
      rename inc (rename ρ^B $ lookup ρ^A v)
        ≡⟨ cong (rename inc) (lookup^R ρ^R v) ⟩
      rename inc (lookup ρ^C v)
    ∎
  ; R⟦var⟧   = λ v ρ^R → lookup^R ρ^R v
  ; embed^BC = refl
  }

fuseSubstitutionRenaming :
  ∀ {Γ Δ Θ σ} (t : Γ ⊢ σ) (ρ : Substitution Γ Δ) (inc : Renaming Δ Θ) →
  rename inc (substitute t ρ) ≡ substitute t (rename inc <$> ρ)
fuseSubstitutionRenaming t inc ρ = Fundamental.lemma fusableSubstitutionRenaming t refl^R

fusableSubstitutions :
  SyntacticFusable SyntacticSubstitution SyntacticSubstitution SyntacticSubstitution
  Equality (λ ρ^A ρ^B ρ^C → `∀[ Equality ] (flip substitute ρ^B <$> ρ^A) ρ^C)
fusableSubstitutions = record
  { 𝓔^R‿∙   = λ {_} {_} {_} {_} {ρ^A} {ρ^B} {ρ^C} {u^B} {u^C} ρ^R eq →
    pack^R $ λ { {_} zero → eq ; (1+ v) →
    begin
      substitute (rename extend (lookup ρ^A v)) (ρ^B `∙ u^B)
        ≡⟨ fuseRenamingSubstitution (lookup ρ^A v) extend (ρ^B `∙ u^B) ⟩
      substitute (lookup ρ^A v) ρ^B
        ≡⟨ lookup^R ρ^R v ⟩
      lookup ρ^C v
    ∎ }
  ; 𝓔^R‿wk  = λ inc {ρ^A} {ρ^B} {ρ^C} ρ^R → pack^R $ λ v →
    begin
      substitute (lookup ρ^A v) (rename inc <$> ρ^B)
           ≡⟨ sym (fuseSubstitutionRenaming (lookup ρ^A v) ρ^B inc) ⟩
      rename inc (substitute (lookup ρ^A v) ρ^B)
           ≡⟨ cong (rename inc) (lookup^R ρ^R v) ⟩
      rename inc (lookup ρ^C v)
    ∎
  ; R⟦var⟧   = λ v ρ^R → lookup^R ρ^R v
  ; embed^BC = refl
  }

fuseSubstitutions :
  ∀ {Γ Δ Θ σ} (t : Γ ⊢ σ) (ρ : Substitution Γ Δ) (ρ′ : Substitution Δ Θ) →
  substitute (substitute t ρ) ρ′ ≡ substitute t (flip substitute ρ′ <$> ρ)
fuseSubstitutions t inc ρ = Fundamental.lemma fusableSubstitutions t refl^R
