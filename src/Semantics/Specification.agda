module Semantics.Specification where

open import Syntax.Core
open import Semantics.Model
open import Semantics.Environment

Kripke : {ℓ^E ℓ^M : Level} → Model ℓ^E → Model ℓ^M →
         Context → Type → Type → Set (ℓ^M ⊔ ℓ^E)
Kripke 𝓔 𝓜 Γ σ τ = {Δ : Context} → Renaming Γ Δ → 𝓔 Δ σ → 𝓜 Δ τ

record Semantics {ℓ^E ℓ^M : Level}
       (𝓔  : Model ℓ^E) (𝓜 : Model ℓ^M) : Set (ℓ^E ⊔ ℓ^M) where
  infixl 5 _⟦$⟧_
  field

    wk      :  Weakening 𝓔
    embed   :  {Γ : Context} → Var Γ ⇒[ 𝓔 ] Γ
    ⟦var⟧   :  {Γ : Context} {σ : Type} → 𝓔 Γ σ → 𝓜 Γ σ
    ⟦λ⟧     :  {Γ : Context} {σ τ : Type} → Kripke 𝓔 𝓜 Γ σ τ → 𝓜 Γ (σ `→ τ)
    _⟦$⟧_   :  Applicative 𝓜
    ⟦⟨⟩⟧    :  {Γ : Context} → 𝓜 Γ `Unit
    ⟦tt⟧    :  {Γ : Context} → 𝓜 Γ `Bool
    ⟦ff⟧    :  {Γ : Context} → 𝓜 Γ `Bool
    ⟦ifte⟧  :  {Γ : Context} {σ : Type} → 𝓜 Γ `Bool → 𝓜 Γ σ → 𝓜 Γ σ → 𝓜 Γ σ


Evaluation : {ℓ^E ℓ^M : Level} (𝓔 : Model ℓ^E) (𝓜 :  Model ℓ^M) → Set (ℓ^M ⊔ ℓ^E)
Evaluation 𝓔 𝓜 = {Γ Δ : Context} {σ : Type} → Γ ⊢ σ → Var Γ ⇒[ 𝓔 ] Δ → 𝓜 Δ σ

Evaluation' : {ℓ^M : Level} (𝓜 :  Model ℓ^M) → Set ℓ^M
Evaluation' 𝓜 = {Γ : Context} {σ : Type} → Γ ⊢ σ → 𝓜 Γ σ

module Fundamental {ℓ^E ℓ^M : Level}
       {𝓔  : Model ℓ^E} {𝓜 : Model ℓ^M} (𝓢 : Semantics 𝓔 𝓜) where
  open Semantics 𝓢

  lemma : Evaluation 𝓔 𝓜
  lemma (`var v)       ρ = ⟦var⟧ (lookup ρ v)
  lemma (t `$ u)       ρ = lemma t ρ ⟦$⟧ lemma u ρ
  lemma (`λ t)         ρ = ⟦λ⟧ (λ inc u → lemma t (wk[ wk ] inc ρ `∙ u))
  lemma `⟨⟩            ρ = ⟦⟨⟩⟧
  lemma `tt            ρ = ⟦tt⟧
  lemma `ff            ρ = ⟦ff⟧
  lemma (`ifte b l r)  ρ = ⟦ifte⟧ (lemma b ρ) (lemma l ρ) (lemma r ρ)

  lemma' : Evaluation' 𝓜
  lemma' t = lemma t embed
