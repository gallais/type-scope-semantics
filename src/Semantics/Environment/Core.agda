module Semantics.Environment.Core where

open import Level as L hiding (zero)
open import Syntax.Context as Context hiding (_<$>_ ; map)
open import Semantics.Model.Core
open import Data.Product hiding (map)
open import Relation.Binary.PropositionalEquality as PEq hiding (refl)

infix 5 Var_⇒[_]_

-- An environment Var Γ ⇒[ 𝓔 ] Δ simply maps each variable of
-- type σ in Γ to an element of type 𝓔 Δ σ.

record Var_⇒[_]_ {A : Set} {ℓ : Level}
                 (Γ : Context A) (𝓔 : Model A ℓ) (Δ : Context A) : Set ℓ where
  constructor pack
  field lookup : {σ : A} (v : σ ∈ Γ) → 𝓔 Δ σ
open Var_⇒[_]_ public

infixr 10 _<$>_
_<$>_ : {A : Set} {ℓ ℓ′ : Level} {Γ Δ θ : Context A} {𝓓 : Model A ℓ} {𝓔 : Model A ℓ′}
        (f : {σ : A} → 𝓓 Δ σ → 𝓔 θ σ) → Var Γ ⇒[ 𝓓 ] Δ → Var Γ ⇒[ 𝓔 ] θ
lookup (f <$> ρ) v = f (lookup ρ v)

-- The simplest example of such an environment is Renaming.
-- It comes with various combinators corresponding to the key
-- elements identified by Altenkirch, Hofmann and Streicher
-- in their 'category of weakenings' in "Categorical reconstruction
-- of a reduction free normalization proof"

Renaming : {A : Set} → Context A → Context A → Set
Renaming Γ Δ = Var Γ ⇒[ _∋_ ] Δ 

map : {A B : Set} {Γ Δ : Context A} (f : A → B) →
      (∀ a b → f a ≡ f b → a ≡ b) →
      Renaming Γ Δ → Renaming (f Context.<$> Γ) (f Context.<$> Δ)
lookup (map f inj inc) v =
  let (σ , eq) = map-inv f v
      v₁       = map⁻¹ f inj (subst (_ ∋_) eq v)
      v₂       = lookup inc v₁
      v₃       = Context.map f v₂
  in subst (_ ∋_) (sym eq) v₃

refl : {A : Set} {Γ : Context A} → Renaming Γ Γ
lookup refl v = v

step : {A : Set} {Γ Δ : Context A} {σ : A} → Renaming Γ Δ → Renaming Γ (Δ ∙ σ)
step ren = 1+_ <$> ren

extend : {A : Set} {Γ : Context A} {σ : A} → Renaming Γ (Γ ∙ σ)
extend = step refl

pop! : {A : Set} {Γ Δ : Context A} {σ : A} → Renaming Γ Δ → Renaming (Γ ∙ σ) (Δ ∙ σ)
lookup (pop! ren) zero   = zero
lookup (pop! ren) (1+ v) = 1+ lookup ren v

-- Renaming naturally gives rise to a notion of weakening for Models
Weakening : (A : Set) {ℓ : Level} → Model A ℓ → Set ℓ
Weakening A 𝓔 = {Γ Δ : Context A} {σ : A} → Renaming Γ Δ → 𝓔 Γ σ → 𝓔 Δ σ

-- And Variables can trivially be renamed:
wk^∋ : {A : Set} → Weakening A _∋_
wk^∋ ren v = lookup ren v
