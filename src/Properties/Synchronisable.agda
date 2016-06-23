module Properties.Synchronisable where

open import Syntax.Core
open import Semantics.Model
open import Semantics.Environment
open import Semantics.Specification hiding (module Fundamental)
open import Properties.Relation

record Synchronisable
  {ℓ^EA ℓ^MA ℓ^EB ℓ^MB ℓ^RE ℓ^RM : Level}
  {𝓔^A  : Model ℓ^EA} {𝓜^A : Model ℓ^MA}
  {𝓔^B  : Model ℓ^EB} {𝓜^B : Model ℓ^MB}
  (𝓢^A  : Semantics 𝓔^A 𝓜^A) (𝓢^B : Semantics 𝓔^B 𝓜^B)
  (𝓔^R  : RModel ℓ^RE 𝓔^A 𝓔^B) (𝓜^R : RModel ℓ^RM 𝓜^A 𝓜^B)
  : Set (ℓ^RE ⊔ ℓ^RM ⊔ ℓ^EA ⊔ ℓ^EB ⊔ ℓ^MA ⊔ ℓ^MB) where

  module 𝓢^A = Semantics 𝓢^A
  module 𝓢^B = Semantics 𝓢^B

  field

    𝓔^R‿wk  :  {Γ Δ Θ : Context} {ρ^A : Var Γ ⇒[ 𝓔^A ] Δ} {ρ^B : Var Γ ⇒[ 𝓔^B ] Δ} →

                  (ren : Renaming Δ Θ) → `∀[ 𝓔^R ] ρ^A ρ^B →
                ----------------------------------------------------------
                  `∀[ 𝓔^R ] (wk[ 𝓢^A.wk ] ren ρ^A) (wk[ 𝓢^B.wk ] ren ρ^B)
               
    R⟦var⟧    :  {Γ Δ : Context} {σ : Type} {ρ^A : Var Γ ⇒[ 𝓔^A ] Δ} {ρ^B : Var Γ ⇒[ 𝓔^B ] Δ}

                   (v : σ ∈ Γ) (ρ^R : `∀[ 𝓔^R ] ρ^A ρ^B) →
                 --------------------------------------------------------------
                   𝓜^R (𝓢^A.⟦var⟧ (lookup ρ^A v)) (𝓢^B.⟦var⟧ (lookup ρ^B v))

    R⟦λ⟧      :  {Γ : Context} {σ τ : Type}
                 {f^A : Kripke 𝓔^A 𝓜^A Γ σ τ} {f^B : Kripke 𝓔^B 𝓜^B Γ σ τ} →

                     RKripke 𝓔^A 𝓔^B 𝓔^R 𝓜^A 𝓜^B 𝓜^R Γ σ τ f^A f^B →
                 -----------------------------------------------------------------------
                     𝓜^R (𝓢^A.⟦λ⟧ f^A) (𝓢^B.⟦λ⟧ f^B)

    R⟦$⟧      :  RApplicative 𝓜^A 𝓜^B 𝓢^A._⟦$⟧_ 𝓢^B._⟦$⟧_ 𝓜^R

    R⟦⟨⟩⟧     :  {Γ : Context} →

                 ------------------------------
                   𝓜^R {Γ} 𝓢^A.⟦⟨⟩⟧ 𝓢^B.⟦⟨⟩⟧
    
    R⟦tt⟧     :  {Γ : Context} →

                 ------------------------------
                   𝓜^R {Γ} 𝓢^A.⟦tt⟧ 𝓢^B.⟦tt⟧
    
    R⟦ff⟧     :  {Γ : Context} →

                 ------------------------------
                   𝓜^R {Γ} 𝓢^A.⟦ff⟧ 𝓢^B.⟦ff⟧
    
    R⟦ifte⟧   :  {Γ : Context} {σ : Type}
                 {b^A : 𝓜^A Γ `Bool} {b^B : 𝓜^B Γ `Bool}
                 {l^A r^A : 𝓜^A Γ σ} {l^B r^B : 𝓜^B Γ σ} →
                 
                   𝓜^R b^A b^B → 𝓜^R l^A l^B → 𝓜^R r^A r^B →
                 ----------------------------------------------------------
                   𝓜^R (𝓢^A.⟦ifte⟧ b^A l^A r^A) (𝓢^B.⟦ifte⟧ b^B l^B r^B)


module Fundamental
  {ℓ^EA ℓ^MA ℓ^EB ℓ^MB ℓ^RE ℓ^RM : Level}
  {𝓔^A  : Model ℓ^EA} {𝓜^A : Model ℓ^MA}
  {𝓔^B  : Model ℓ^EB} {𝓜^B : Model ℓ^MB}
  {𝓢^A  : Semantics 𝓔^A 𝓜^A} {𝓢^B : Semantics 𝓔^B 𝓜^B}
  {𝓔^R  : RModel ℓ^RE 𝓔^A 𝓔^B} {𝓜^R : RModel ℓ^RM 𝓜^A 𝓜^B}
  (𝓡 : Synchronisable 𝓢^A 𝓢^B 𝓔^R 𝓜^R)
  where

  open Synchronisable 𝓡
  eval = Semantics.Specification.Fundamental.lemma

  lemma :  {Γ Δ : Context} {σ : Type} (t : Γ ⊢ σ)
           {ρ^A : Var Γ ⇒[ 𝓔^A ] Δ} {ρ^B : Var Γ ⇒[ 𝓔^B ] Δ} (ρ^R : `∀[ 𝓔^R ] ρ^A ρ^B) →
           𝓜^R (eval 𝓢^A t ρ^A) (eval 𝓢^B t ρ^B)
  lemma (`var v)       ρ^R = R⟦var⟧ v ρ^R
  lemma (f `$ t)       ρ^R = R⟦$⟧ (lemma f ρ^R) (lemma t ρ^R)
  lemma (`λ t)         ρ^R = R⟦λ⟧ (λ inc u^R → lemma t (𝓔^R‿wk inc ρ^R ∙^R u^R))
  lemma `⟨⟩            ρ^R = R⟦⟨⟩⟧
  lemma `tt            ρ^R = R⟦tt⟧
  lemma `ff            ρ^R = R⟦ff⟧
  lemma (`ifte b l r)  ρ^R = R⟦ifte⟧ (lemma b ρ^R) (lemma l ρ^R) (lemma r ρ^R)
