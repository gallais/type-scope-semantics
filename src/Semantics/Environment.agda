module Semantics.Environment where

open import Syntax.Core hiding (_<$>_)
open import Semantics.Model
open import Semantics.Environment.Core as EC hiding (Var_⇒[_]_ ; Weakening) public

Var_⇒[_]_ = EC.Var_⇒[_]_ {Type}
Weakening = EC.Weakening Type

-- Parallel substitutions are quite evidently environments:
Substitution : Context → Context → Set
Substitution Γ Δ = Var Γ ⇒[ _⊢_ ] Δ

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
