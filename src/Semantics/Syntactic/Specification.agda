module Semantics.Syntactic.Specification where

open import Syntax.Core
open import Semantics.Model
open import Semantics.Environment
open import Semantics.Specification as Semantics hiding (module Fundamental)

record Syntactic {ℓ : Level} (𝓔 : Model ℓ) : Set ℓ where
  field  embed  : {Γ : Context} → Var Γ ⇒[ 𝓔 ] Γ
         wk     : Weakening 𝓔
         ⟦var⟧  : {Γ : Context} {σ : Type} → 𝓔 Γ σ → Γ ⊢ σ

module Fundamental {ℓ : Level} {𝓔 : Model ℓ} (𝓢 : Syntactic 𝓔) where

  open Syntactic 𝓢

  syntactic : Semantics 𝓔 _⊢_
  syntactic = record
    { wk      = wk; embed   = embed; ⟦var⟧   = ⟦var⟧
    ; ⟦λ⟧     = λ t → `λ (t (step refl) (lookup embed zero))
    ; _⟦$⟧_   = _`$_; ⟦⟨⟩⟧ = `⟨⟩; ⟦tt⟧ = `tt; ⟦ff⟧ = `ff; ⟦ifte⟧  = `ifte }

  lemma : {Δ Γ : Context} {σ : Type} → Γ ⊢ σ → Var Γ ⇒[ 𝓔 ] Δ → Δ ⊢ σ
  lemma = Semantics.Fundamental.lemma syntactic
