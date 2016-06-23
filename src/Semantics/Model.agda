module Semantics.Model where

open import Level as L using (Level ; _⊔_) public
open import Syntax.Core
open import Syntax.Normal

Model : (ℓ : Level) → Set (L.suc ℓ)
Model ℓ = Context → Type → Set ℓ

Applicative : {ℓ : Level} → Model ℓ → Set ℓ
Applicative 𝓜 = {Γ : Context} {σ τ : Type} → 𝓜 Γ (σ `→ τ) → 𝓜 Γ σ → 𝓜 Γ τ

Reify : {ℓ : Level} → (Type → Set) → Model ℓ → Set ℓ
Reify R 𝓜 = {Γ : Context} (σ : Type) → 𝓜 Γ σ → Γ ⊢[ R ]^nf σ

Reflect : {ℓ : Level} → (Type → Set) → Model ℓ → Set ℓ
Reflect R 𝓔 = {Γ : Context} (σ : Type) → Γ ⊢[ R ]^ne σ → 𝓔 Γ σ
