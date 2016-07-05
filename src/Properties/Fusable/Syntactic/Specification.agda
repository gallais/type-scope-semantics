module Properties.Fusable.Syntactic.Specification where

open import Syntax.Core
open import Semantics.Model
open import Semantics.Environment hiding (refl)
open import Semantics.Specification hiding (module Fundamental)
open import Semantics.Syntactic.Specification hiding (module Fundamental)
open import Properties.Relation
open import Relation.Binary.PropositionalEquality

record SyntacticFusable
  {ℓ^EA ℓ^EB ℓ^EC ℓ^REBC ℓ^RE : Level}
  {𝓔^A : Model ℓ^EA} {𝓔^B : Model ℓ^EB} {𝓔^C : Model ℓ^EC}
  (𝓢^A : Syntactic 𝓔^A) (𝓢^B : Syntactic 𝓔^B) (𝓢^C : Syntactic 𝓔^C)
  (𝓔^R‿BC : RModel ℓ^REBC 𝓔^B 𝓔^C)
  (𝓔^R : ∀ {Θ Δ Γ} → Var Γ ⇒[ 𝓔^A ] Δ → Var Δ ⇒[ 𝓔^B ] Θ → Var Γ ⇒[ 𝓔^C ] Θ → Set ℓ^RE)
  : Set (ℓ^RE ⊔ ℓ^REBC ⊔ ℓ^EC ⊔ ℓ^EB ⊔ ℓ^EA)
  where

  module 𝓢^A = Syntactic 𝓢^A
  module 𝓢^B = Syntactic 𝓢^B
  module 𝓢^C = Syntactic 𝓢^C

  𝓡 : ∀ {Γ Δ Θ σ} → Γ ⊢ σ → Var Γ ⇒[ 𝓔^A ] Δ → Var Δ ⇒[ 𝓔^B ] Θ → Var Γ ⇒[ 𝓔^C ] Θ → Set _
  𝓡 t ρ^A ρ^B ρ^C =
    let open Semantics.Syntactic.Specification.Fundamental
    in lemma 𝓢^B (lemma 𝓢^A t ρ^A) ρ^B ≡ lemma 𝓢^C t ρ^C

  field
  
    𝓔^R‿∙ : ∀ {Γ Δ Θ σ} {ρ^A : Var Γ ⇒[ 𝓔^A ] Δ} → ∀ {ρ^B ρ^C u^B} {u^C : 𝓔^C Θ σ} →
             𝓔^R ρ^A ρ^B ρ^C → related 𝓔^R‿BC u^B u^C →
             𝓔^R  (wk[ 𝓢^A.wk ] extend ρ^A `∙ lookup 𝓢^A.embed zero)
                  (ρ^B `∙ u^B) (ρ^C `∙ u^C)

    𝓔^R‿wk : ∀ {Γ Δ Θ E} (inc : Renaming Θ E) → {ρ^A : Var Γ ⇒[ 𝓔^A ] Δ} → ∀ {ρ^B ρ^C} →
              𝓔^R ρ^A ρ^B ρ^C → 𝓔^R ρ^A (wk[ 𝓢^B.wk ] inc ρ^B) (wk[ 𝓢^C.wk ] inc ρ^C)

    R⟦var⟧ : ∀ {Γ Δ Θ σ} (v : σ ∈ Γ) → ∀ {ρ^A ρ^C} {ρ^B : Var Δ ⇒[ 𝓔^B ] Θ} →
              𝓔^R ρ^A ρ^B ρ^C → 𝓡 (`var v) ρ^A ρ^B ρ^C

    embed^BC : ∀ {Γ σ} → related 𝓔^R‿BC {Γ ∙ σ} (lookup 𝓢^B.embed zero) (lookup 𝓢^C.embed zero)


module Fundamental
  {ℓ^EA ℓ^EB ℓ^EC ℓ^REBC ℓ^RE : Level}
  {𝓔^A : Model ℓ^EA} {𝓔^B : Model ℓ^EB} {𝓔^C : Model ℓ^EC}
  {𝓢^A : Syntactic 𝓔^A} {𝓢^B : Syntactic 𝓔^B} {𝓢^C : Syntactic 𝓔^C}
  {𝓔^R‿BC : RModel ℓ^REBC 𝓔^B 𝓔^C}
  {𝓔^R : ∀ {Θ Δ Γ} → Var Γ ⇒[ 𝓔^A ] Δ → Var Δ ⇒[ 𝓔^B ] Θ → Var Γ ⇒[ 𝓔^C ] Θ → Set ℓ^RE}
  (𝓕 : SyntacticFusable 𝓢^A 𝓢^B 𝓢^C 𝓔^R‿BC 𝓔^R)
  where

  open SyntacticFusable 𝓕
  open import Properties.Fusable.Specification
  open import Data.Product

  𝓜^A = Semantics.Syntactic.Specification.Fundamental.syntactic 𝓢^A
  𝓜^B = Semantics.Syntactic.Specification.Fundamental.syntactic 𝓢^B
  𝓜^C = Semantics.Syntactic.Specification.Fundamental.syntactic 𝓢^C
  
  syntactic : Fusable 𝓜^A 𝓜^B 𝓜^C 𝓔^R‿BC 𝓔^R (mkRModel _≡_)
  syntactic = record
    { reify^A   = λ t → t
    ; 𝓔^R‿∙    = 𝓔^R‿∙
    ; 𝓔^R‿wk   = 𝓔^R‿wk
    ; R⟦var⟧    = R⟦var⟧
    ; R⟦$⟧      = λ f t ρ^R → cong₂ _`$_
    ; R⟦λ⟧      = λ t ρ^R r → cong `λ (r extend embed^BC)
    ; R⟦⟨⟩⟧     = λ ρ^R → refl
    ; R⟦tt⟧     = λ ρ^R → refl
    ; R⟦ff⟧     = λ ρ^R → refl
    ; R⟦ifte⟧   = λ b l r ρ^R eqb eql → cong₂ (uncurry `ifte) (cong₂ _,_ eqb eql)
    }

  lemma : ∀ {Γ Δ Θ σ} (t : Γ ⊢ σ) → ∀ {ρ^A ρ^C} {ρ^B : Var Δ ⇒[ 𝓔^B ] Θ} →
          𝓔^R ρ^A ρ^B ρ^C → 𝓡 t ρ^A ρ^B ρ^C
  lemma = Fundamental.lemma syntactic
