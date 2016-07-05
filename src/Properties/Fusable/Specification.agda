module Properties.Fusable.Specification where

open import Syntax.Core
open import Semantics.Model
open import Semantics.Environment
open import Semantics.Specification hiding (module Fundamental)
open import Properties.Relation

record Fusable
  {ℓ^EA ℓ^MA ℓ^EB ℓ^MB ℓ^EC ℓ^MC ℓ^RE ℓ^REBC ℓ^RM : Level}
  {𝓔^A : Model ℓ^EA} {𝓔^B : Model ℓ^EB} {𝓔^C : Model ℓ^EC}
  {𝓜^A : Model ℓ^MA} {𝓜^B : Model ℓ^MB} {𝓜^C : Model ℓ^MC}
  (𝓢^A : Semantics 𝓔^A 𝓜^A) (𝓢^B : Semantics 𝓔^B 𝓜^B) (𝓢^C : Semantics 𝓔^C 𝓜^C)
  (𝓔^R‿BC : RModel ℓ^REBC 𝓔^B 𝓔^C)
  (𝓔^R : ∀ {Θ Δ Γ} → Var Γ ⇒[ 𝓔^A ] Δ → Var Δ ⇒[ 𝓔^B ] Θ → Var Γ ⇒[ 𝓔^C ] Θ → Set ℓ^RE)
  (𝓜^R : RModel ℓ^RM 𝓜^B 𝓜^C)
  : Set (ℓ^RM ⊔ ℓ^RE ⊔ ℓ^EC ⊔ ℓ^EB ⊔ ℓ^EA ⊔ ℓ^MA ⊔ ℓ^REBC) where

  -- Semantics
  module 𝓢^A = Semantics 𝓢^A
  module 𝓢^B = Semantics 𝓢^B
  module 𝓢^C = Semantics 𝓢^C

  field

    reify^A : ∀ {Γ σ} → 𝓜^A Γ σ → Γ ⊢ σ

  -- We interrupt the list of fields here to introduce a handy
  -- notation describing the generic way in which 𝓜^R is used
  -- throughout the definition

  𝓡 : ∀ {Γ Δ Θ σ} → Γ ⊢ σ → Var Γ ⇒[ 𝓔^A ] Δ → Var Δ ⇒[ 𝓔^B ] Θ → Var Γ ⇒[ 𝓔^C ] Θ → Set _
  𝓡 t ρ^A ρ^B ρ^C =
    let open Semantics.Specification.Fundamental in
    related 𝓜^R (lemma 𝓢^B (reify^A (lemma 𝓢^A t ρ^A)) ρ^B) (lemma 𝓢^C t ρ^C)

  -- We can now go back to the specification of the Fusable
  -- Semantics.

  field

    𝓔^R‿∙ : ∀ {Γ Δ Θ σ} {ρ^A : Var Γ ⇒[ 𝓔^A ] Δ} → ∀ {ρ^B ρ^C u^B} {u^C : 𝓔^C Θ σ} →
             𝓔^R ρ^A ρ^B ρ^C → related 𝓔^R‿BC u^B u^C →
             𝓔^R  (wk[ 𝓢^A.wk ] extend ρ^A `∙ lookup 𝓢^A.embed zero)
                  (ρ^B `∙ u^B) (ρ^C `∙ u^C)

    𝓔^R‿wk : ∀ {Γ Δ Θ E} (inc : Renaming Θ E) → {ρ^A : Var Γ ⇒[ 𝓔^A ] Δ} → ∀ {ρ^B ρ^C} →
              𝓔^R ρ^A ρ^B ρ^C → 𝓔^R ρ^A (wk[ 𝓢^B.wk ] inc ρ^B) (wk[ 𝓢^C.wk ] inc ρ^C)

    R⟦var⟧ : ∀ {Γ Δ Θ σ} (v : σ ∈ Γ) → ∀ {ρ^A ρ^C} {ρ^B : Var Δ ⇒[ 𝓔^B ] Θ} →
              𝓔^R ρ^A ρ^B ρ^C → 𝓡 (`var v) ρ^A ρ^B ρ^C

    R⟦λ⟧ : ∀ {Γ Δ Θ σ τ} (b : Γ ∙ σ ⊢ τ) → ∀ {ρ^A ρ^C} {ρ^B : Var Δ ⇒[ 𝓔^B ] Θ} →
           𝓔^R ρ^A ρ^B ρ^C →
           (r :  ∀ {E} (inc : Renaming Θ E) → ∀ {u^B u^C} → related 𝓔^R‿BC u^B u^C →
            let  ρ^A′ =  wk[ 𝓢^A.wk ] extend ρ^A `∙ lookup 𝓢^A.embed zero
                 ρ^B′ =  wk[ 𝓢^B.wk ] inc ρ^B `∙ u^B
                 ρ^C′ =  wk[ 𝓢^C.wk ] inc ρ^C `∙ u^C
            in 𝓡 b ρ^A′ ρ^B′ ρ^C′) →
           𝓡 (`λ b) ρ^A ρ^B ρ^C

    R⟦$⟧ : ∀ {Γ Δ Θ σ τ} (f : Γ ⊢ σ `→ τ) (t : Γ ⊢ σ) →
           ∀ {ρ^A ρ^C} {ρ^B : Var Δ ⇒[ 𝓔^B ] Θ} → 𝓔^R ρ^A ρ^B ρ^C →
           𝓡 f ρ^A ρ^B ρ^C → 𝓡 t ρ^A ρ^B ρ^C → 𝓡 (f `$ t) ρ^A ρ^B ρ^C

    R⟦⟨⟩⟧ : ∀ {Γ Δ Θ} {ρ^A : Var Γ ⇒[ 𝓔^A ] Δ} {ρ^B : Var Δ ⇒[ 𝓔^B ] Θ} → ∀ {ρ^C} →
            𝓔^R ρ^A ρ^B ρ^C → 𝓡 `⟨⟩ ρ^A ρ^B ρ^C
    R⟦tt⟧ : ∀ {Γ Δ Θ} {ρ^A : Var Γ ⇒[ 𝓔^A ] Δ} {ρ^B : Var Δ ⇒[ 𝓔^B ] Θ} → ∀ {ρ^C} →
            𝓔^R ρ^A ρ^B ρ^C → 𝓡 `tt ρ^A ρ^B ρ^C
    R⟦ff⟧ : ∀ {Γ Δ Θ} {ρ^A : Var Γ ⇒[ 𝓔^A ] Δ} {ρ^B : Var Δ ⇒[ 𝓔^B ] Θ} → ∀ {ρ^C} →
            𝓔^R ρ^A ρ^B ρ^C → 𝓡 `ff ρ^A ρ^B ρ^C

    R⟦ifte⟧ : ∀ {Γ Δ Θ σ} (b : Γ ⊢ `Bool) (l r : Γ ⊢ σ) →
              ∀ {ρ^A ρ^C} {ρ^B : Var Δ ⇒[ 𝓔^B ] Θ} → 𝓔^R ρ^A ρ^B ρ^C →
              𝓡 b ρ^A ρ^B ρ^C → 𝓡 l ρ^A ρ^B ρ^C → 𝓡 r ρ^A ρ^B ρ^C →
              𝓡 (`ifte b l r) ρ^A ρ^B ρ^C

module Fundamental
  {ℓ^EA ℓ^MA ℓ^EB ℓ^MB ℓ^EC ℓ^MC ℓ^RE ℓ^REBC ℓ^RM : Level}
  {𝓔^A : Model ℓ^EA} {𝓔^B : Model ℓ^EB} {𝓔^C : Model ℓ^EC}
  {𝓜^A : Model ℓ^MA} {𝓜^B : Model ℓ^MB} {𝓜^C : Model ℓ^MC}
  {𝓢^A : Semantics 𝓔^A 𝓜^A} {𝓢^B : Semantics 𝓔^B 𝓜^B} {𝓢^C : Semantics 𝓔^C 𝓜^C}
  {𝓔^R‿BC : RModel ℓ^REBC 𝓔^B 𝓔^C}
  {𝓔^R : ∀ {Θ Δ Γ} → Var Γ ⇒[ 𝓔^A ] Δ → Var Δ ⇒[ 𝓔^B ] Θ → Var Γ ⇒[ 𝓔^C ] Θ → Set ℓ^RE}
  {𝓜^R : RModel ℓ^RM 𝓜^B 𝓜^C}
  (𝓕 : Fusable 𝓢^A 𝓢^B 𝓢^C 𝓔^R‿BC 𝓔^R 𝓜^R)
  where

  open Fusable 𝓕

  lemma : ∀ {Γ Δ Θ σ} (t : Γ ⊢ σ) → ∀ {ρ^A ρ^C} {ρ^B : Var Δ ⇒[ 𝓔^B ] Θ} →
          𝓔^R ρ^A ρ^B ρ^C → 𝓡 t ρ^A ρ^B ρ^C
  lemma (`var v)       ρ^R = R⟦var⟧ v ρ^R
  lemma (f `$ t)       ρ^R = R⟦$⟧ f t ρ^R (lemma f ρ^R) (lemma t ρ^R)
  lemma (`λ t)         ρ^R = R⟦λ⟧ t ρ^R (λ inc u^R → lemma t (𝓔^R‿∙ (𝓔^R‿wk inc ρ^R) u^R))
  lemma `⟨⟩            ρ^R = R⟦⟨⟩⟧ ρ^R
  lemma `tt            ρ^R = R⟦tt⟧ ρ^R
  lemma `ff            ρ^R = R⟦ff⟧ ρ^R
  lemma (`ifte b l r)  ρ^R = R⟦ifte⟧ b l r ρ^R (lemma b ρ^R) (lemma l ρ^R) (lemma r ρ^R)
