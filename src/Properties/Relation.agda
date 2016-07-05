module Properties.Relation where

open import Level hiding (zero)
open import Syntax.Type
open import Syntax.Context hiding (_∋_)
open import Semantics.Model
open import Semantics.Environment
open import Semantics.Specification
open import Function
open import Relation.Binary.PropositionalEquality as PropEq

record RModel
  {ℓ^A ℓ^B : Level} (ℓ^R : Level)
  (𝓜^A : Model ℓ^A) (𝓜^B : Model ℓ^B)
  : Set (suc ℓ^R ⊔ ℓ^B ⊔ ℓ^A) where
  constructor mkRModel
  field related : {Γ : Context} {σ : Type} → 𝓜^A Γ σ → 𝓜^B Γ σ → Set ℓ^R
open RModel public

Equality : {ℓ : Level} {𝓜 : Model ℓ} → RModel _ 𝓜 𝓜
Equality = mkRModel _≡_

Symmetric : {ℓ^A ℓ^R : Level} {𝓜^A : Model ℓ^A} → RModel ℓ^R 𝓜^A 𝓜^A → Set (ℓ^R ⊔ ℓ^A)
Symmetric {𝓜^A = 𝓜^A} 𝓜^R = {Γ : Context} {σ : Type} {T U : 𝓜^A Γ σ} →
  related 𝓜^R T U → related 𝓜^R U T

Transitive : {ℓ^A ℓ^R : Level} {𝓜^A : Model ℓ^A} → RModel ℓ^R 𝓜^A 𝓜^A → Set (ℓ^R ⊔ ℓ^A)
Transitive {𝓜^A = 𝓜^A} 𝓜^R = {Γ : Context} {σ : Type} {S T U : 𝓜^A Γ σ} →
  related 𝓜^R S T → related 𝓜^R T U → related 𝓜^R S U

RKripke :
  {ℓ^EA ℓ^EB ℓ^MA ℓ^MB : Level} {ℓ^ER ℓ^MR : Level}
  {𝓔^A : Model ℓ^EA} {𝓔^B : Model ℓ^EB} (𝓔^R : RModel ℓ^ER 𝓔^A 𝓔^B) →
  {𝓜^A : Model ℓ^MA} {𝓜^B : Model ℓ^MB} (𝓜^R : RModel ℓ^MR 𝓜^A 𝓜^B) →
  {Γ : Context} {σ τ : Type} → Kripke 𝓔^A 𝓜^A Γ σ τ → Kripke 𝓔^B 𝓜^B Γ σ τ →
  Set (ℓ^MR ⊔ (ℓ^ER ⊔ (ℓ^EB ⊔ ℓ^EA)))
RKripke {𝓔^A = 𝓔^A} {𝓔^B} 𝓔^R 𝓜^R {Γ} {σ} {τ} f^A f^B =
  {Δ : Context} (ren : Renaming Γ Δ) {u^A : 𝓔^A Δ σ} {u^B : 𝓔^B Δ σ}
  (u^R : related 𝓔^R u^A u^B) → related 𝓜^R  (f^A ren u^A) (f^B ren u^B)

RApplicative : {ℓ^A ℓ^B ℓ^R : Level} {𝓜^A : Model ℓ^A} {𝓜^B : Model ℓ^B} →
               Applicative 𝓜^A → Applicative 𝓜^B → RModel ℓ^R 𝓜^A 𝓜^B →
               Set (ℓ^R ⊔ (ℓ^B ⊔ ℓ^A))
RApplicative {𝓜^A = 𝓜^A} {𝓜^B} _$$^A_ _$$^B_ 𝓜^R =
  {Γ : Context} {σ τ : Type}
  {f^A : 𝓜^A Γ (σ `→ τ)} {f^B : 𝓜^B Γ (σ `→ τ)}
  {t^A : 𝓜^A Γ σ} {t^B : 𝓜^B Γ σ} →
  
    related 𝓜^R f^A f^B → related 𝓜^R t^A t^B →
  -----------------------------------------------
    related 𝓜^R (f^A $$^A t^A) (f^B $$^B t^B)


record `∀[_] {ℓ^A ℓ^B ℓ^R : Level}
  {𝓔^A : Model ℓ^A} {𝓔^B : Model ℓ^B} (𝓔^R : RModel ℓ^R 𝓔^A 𝓔^B)
  {Γ Δ : Context} (ρ^A : Var Γ ⇒[ 𝓔^A ] Δ) (ρ^B : Var Γ ⇒[ 𝓔^B ] Δ) : Set ℓ^R where
  constructor pack^R
  field lookup^R : {σ : Type} (v : σ ∈ Γ) → related 𝓔^R (lookup ρ^A v) (lookup ρ^B v)
open `∀[_] public

ε^R : {ℓ^A ℓ^B ℓ^R : Level} {𝓔^A : Model ℓ^A} {𝓔^B : Model ℓ^B} {𝓔^R : RModel ℓ^R 𝓔^A 𝓔^B} →
      {Γ : Context} → `∀[ 𝓔^R ] (Var ε ⇒[ 𝓔^A ] Γ ∋ `ε) `ε
lookup^R ε^R ()

_∙^R_ :
  {ℓ^A ℓ^B ℓ^R : Level} {𝓔^A : Model ℓ^A} {𝓔^B : Model ℓ^B} {𝓔^R : RModel ℓ^R 𝓔^A 𝓔^B} →
  {Δ Γ : Context} {ρ^A : Var Γ ⇒[ 𝓔^A ] Δ} {ρ^B : Var Γ ⇒[ 𝓔^B ] Δ} (ρ^R : `∀[ 𝓔^R ] ρ^A ρ^B)
  {σ : Type} {u^A : 𝓔^A Δ σ} {u^B : 𝓔^B Δ σ} → related 𝓔^R u^A u^B →
  `∀[ 𝓔^R ] (ρ^A `∙ u^A) (ρ^B `∙ u^B)
lookup^R (ρ^R ∙^R u^R) zero    = u^R
lookup^R (ρ^R ∙^R u^R) (1+ v)  = lookup^R ρ^R v

_∙^R′_ :
  {ℓ^A ℓ^B ℓ^R : Level} {𝓔^A : Model ℓ^A} {𝓔^B : Model ℓ^B} {𝓔^R : RModel ℓ^R 𝓔^A 𝓔^B} →
  {Δ Γ : Context} {σ : Type}  {ρ^A : Var (Γ ∙ σ) ⇒[ 𝓔^A ] Δ} {ρ^B : Var Γ ∙ σ ⇒[ 𝓔^B ] Δ}
  (ρ^R : ∀ {σ} (v : σ ∈ Γ) → related 𝓔^R (lookup ρ^A (1+ v)) (lookup ρ^B (1+ v))) →
  related 𝓔^R (lookup ρ^A zero) (lookup ρ^B zero) →
  `∀[ 𝓔^R ] ρ^A ρ^B
lookup^R (ρ^R ∙^R′ u^R) zero    = u^R
lookup^R (ρ^R ∙^R′ u^R) (1+ v)  = ρ^R v

refl^R : {ℓ : Level} {𝓔 : Model ℓ} {Γ Δ : Context} {ρ : Var Γ ⇒[ 𝓔 ] Δ} → `∀[ Equality ] ρ ρ
refl^R = pack^R (λ _ → PropEq.refl)
