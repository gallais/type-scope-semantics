module Semantics.Erasure where

open import Data.Nat
open import Data.Fin
open import Function hiding (_∋_)

open import Syntax.Core
open import Syntax.RawTerms
open import Semantics.Model
open import Semantics.Environment
open import Semantics.Specification

RawModel : (ℕ → Set) → Model _
RawModel 𝓜 Γ _ = 𝓜 (length Γ)

erase^∈ : ∀ {Γ} {σ : Type} → σ ∈ Γ → Fin (length Γ)
erase^∈ zero   = zero
erase^∈ (1+ x) = suc (erase^∈ x)

ERS : Semantics (_∋_) (RawModel Raw)
Semantics.wk     ERS = λ ρ → lookup ρ
Semantics.embed  ERS = pack id
Semantics.⟦var⟧  ERS = `var ∘ erase^∈
Semantics.⟦λ⟧    ERS = λ {_} {σ} b → `λ σ (b (step {σ = σ} refl) zero)
Semantics._⟦$⟧_  ERS = _`$_
Semantics.⟦⟨⟩⟧   ERS = `⟨⟩
Semantics.⟦tt⟧   ERS = `tt
Semantics.⟦ff⟧   ERS = `ff
Semantics.⟦ifte⟧ ERS = `ifte

erase^⊢ : ∀ {Γ σ} → Γ ⊢ σ → Raw (length Γ)
erase^⊢ t = Fundamental.lemma ERS t (pack id)
