module Semantics.Environment where

open import Syntax.Core
open import Semantics.Model

infix 5 Var_⇒[_]_

-- An environment Var Γ ⇒[ 𝓔 ] Δ simply maps each variable of
-- type σ in Γ to an element of type 𝓔 Δ σ.

record Var_⇒[_]_ {ℓ : Level} (Γ : Context) (𝓔 : Model ℓ) (Δ : Context) : Set ℓ where
  constructor pack
  field lookup : {σ : Type} (v : σ ∈ Γ) → 𝓔 Δ σ
open Var_⇒[_]_ public

infixr 10 _<$>_
_<$>_ : {ℓ ℓ′ : Level} {Γ Δ θ : Context} {𝓓 : Model ℓ} {𝓔 : Model ℓ′}
        (f : {σ : Type} → 𝓓 Δ σ → 𝓔 θ σ) → Var Γ ⇒[ 𝓓 ] Δ → Var Γ ⇒[ 𝓔 ] θ
lookup (f <$> ρ) v = f (lookup ρ v)

-- Parallel substitutions are quite evidently environments:
Substitution : Context → Context → Set
Substitution Γ Δ = Var Γ ⇒[ _⊢_ ] Δ

-- However, the simplest example of such an environment is Renaming.
-- It comes with various combinators corresponding to the key
-- elements identified by Altenkirch, Hofmann and Streicher
-- in their 'category of weakenings' in "Categorical reconstruction
-- of a reduction free normalization proof"

Renaming : Context → Context → Set
Renaming Γ Δ = Var Γ ⇒[ _∋_ ] Δ 

refl : {Γ : Context} → Renaming Γ Γ
lookup refl v = v

step : {Γ Δ : Context} {σ : Type} → Renaming Γ Δ → Renaming Γ (Δ ∙ σ)
step ren = 1+_ <$> ren

extend : {Γ : Context} {σ : Type} → Renaming Γ (Γ ∙ σ)
extend = step refl

pop! : {Γ Δ : Context} {σ : Type} → Renaming Γ Δ → Renaming (Γ ∙ σ) (Δ ∙ σ)
lookup (pop! ren) zero   = zero
lookup (pop! ren) (1+ v) = 1+ lookup ren v

-- Renaming naturally gives rise to a notion of weakening for Models
Weakening : {ℓ : Level} → Model ℓ → Set ℓ
Weakening 𝓔 = {Γ Δ : Context} {σ : Type} → Renaming Γ Δ → 𝓔 Γ σ → 𝓔 Δ σ

-- And Variables can trivially be renamed:
wk^∋ : Weakening _∋_
wk^∋ ren v = lookup ren v

-- We can naturally define simple combinators for the empty
-- environment and the extension of an existing environment
-- with an extra value.

`ε : {ℓ : Level} {Δ : Context} {𝓔 : Model ℓ} → Var ε ⇒[ 𝓔 ] Δ
lookup `ε ()

infixl 10 _`∙_
_`∙_ : {ℓ : Level} {Γ Δ : Context} {𝓔 : Model ℓ} {σ : Type} →
       Var Γ ⇒[ 𝓔 ] Δ → 𝓔 Δ σ → Var (Γ ∙ σ) ⇒[ 𝓔 ] Δ
lookup (ρ `∙ s) zero    = s
lookup (ρ `∙ s) (1+ n)  = lookup ρ n

-- If values in a model can be weakened so can an environment
-- of such values

wk[_] :  {ℓ : Level} {Δ : Context} {𝓔 : Model ℓ} (wk : Weakening 𝓔)
         {Γ Θ : Context} → Renaming Δ Θ → Var Γ ⇒[ 𝓔 ] Δ → Var Γ ⇒[ 𝓔 ] Θ
wk[ wk ] ren ρ = wk ren <$> ρ

-- A weak form of transitivity: any environment may be pre-composed
-- with a renaming to yield another environment.
trans : {ℓ : Level} {Γ Δ Θ : Context} {𝓔 : Model ℓ} →
        Renaming Γ Δ → Var Δ ⇒[ 𝓔 ] Θ → Var Γ ⇒[ 𝓔 ] Θ
trans ren env = lookup env <$> ren
