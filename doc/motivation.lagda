\begin{code}
module motivation where

open import Data.List hiding ([_])
open import Function

data Type : Set where
  base : Type
  arr  : Type → Type → Type

Cx' = List Type
Model' = Type → Cx' → Set

infixr 8 _⇒_
_⇒_ : (Cx' → Set) → (Cx' → Set) → Cx' → Set
(f ⇒ g) Γ = f Γ → g Γ

[_]' : (Cx' → Set) → Set
[ P ]' = ∀ {x} → P x

infix 9 _⊢_
_⊢_ : Type → (Cx' → Set) → Cx' → Set
(σ ⊢ T) Γ = T (σ ∷ Γ)


data Var : Model' where
  ze : ∀ {σ} → [ σ ⊢ Var σ ]'
  su : ∀ {σ τ} → [ Var σ ⇒ τ ⊢ Var σ ]'

□ : (Cx' → Set) → (Cx' → Set)
□ P Γ = ∀ {Δ} → (∀ {σ} → Var σ Γ → Var σ Δ) → P Δ


data Tm : Model' where
  `var : ∀ {σ} → [ Var σ ⇒ Tm σ ]'
  _`$_ : ∀ {σ τ} → [ Tm (arr σ τ) ⇒ Tm σ ⇒ Tm τ ]'
  `λ   : ∀ {σ τ} → [ σ ⊢ Tm τ ⇒ Tm (arr σ τ) ]'
\end{code}
%<*ren>
\begin{code}
ren : {Γ Δ : List Type} → (∀ {σ} → Var σ Γ → Var σ Δ) → (∀ {σ} → Tm σ Γ → Tm σ Δ)
ren ρ (`var v)  = `var (ρ v)
ren ρ (f `$ t)  = ren ρ f `$ ren ρ t
ren ρ (`λ b)    = `λ (ren ((su ∘ ρ) -, ze) b)
\end{code}
%</ren>
\begin{code}
  where 

  _-,_ : ∀ {Γ σ Δ} → (∀ {τ} → Var τ Γ → Var τ Δ) → Var σ Δ → ∀ {τ} → Var τ (σ ∷ Γ) → Var τ Δ
  (ρ -, v) ze     = v
  (ρ -, v) (su k) = ρ k
\end{code}
%<*sub>
\begin{code}
sub : {Γ Δ : List Type} → (∀ {σ} → Var σ Γ → Tm σ Δ) → (∀ {σ} → Tm σ Γ → Tm σ Δ)
sub ρ (`var v)  = ρ v
sub ρ (f `$ t)  = sub ρ f `$ sub ρ t
sub ρ (`λ b)    = `λ (sub ((ren su ∘ ρ) -, `var ze) b)
\end{code}
%</sub>
\begin{code}
  where

  _-,_ :  ∀ {Γ σ Δ} → (∀ {τ} → Var τ Γ → Tm τ Δ) → Tm σ Δ → ∀ {τ} → Var τ (σ ∷ Γ) → Tm τ Δ
  (ρ -, v) ze     = v
  (ρ -, v) (su k) = ρ k

record Kit (◆ : Model') : Set where
  field
    var : ∀ {σ} → [ ◆ σ ⇒ Tm σ ]'
    zro : ∀ {σ} → [ σ ⊢ ◆ σ ]'
    wkn : ∀ {σ τ} → [ ◆ τ ⇒ σ ⊢ ◆ τ ]'

module kitkit {◆ : Model'} (κ : Kit ◆) where
\end{code}
%<*kit>
\begin{code}
 kit : {Γ Δ : List Type} → (∀ {σ} → Var σ Γ → ◆ σ Δ) → (∀ {σ} → Tm σ Γ → Tm σ Δ)
 kit ρ (`var v)  = Kit.var κ (ρ v)
 kit ρ (f `$ t)  = kit ρ f `$ kit ρ t
 kit ρ (`λ b)    = `λ (kit ((Kit.wkn κ ∘ ρ) -, Kit.zro κ) b)
\end{code}
%</kit>
\begin{code}
    where

    _-,_ :  ∀ {Γ σ Δ} → (∀ {τ} → Var τ Γ → ◆ τ Δ) → ◆ σ Δ → ∀ {τ} → Var τ (σ ∷ Γ) → ◆ τ Δ
    (ρ -, v) ze    = v
    (ρ -, v) (su k) = ρ k

Val : Model'
Val base      Γ = Tm base Γ
Val (arr σ τ) Γ = ∀ {Δ} → (∀ {ν} → Var ν Γ → Var ν Δ) → Val σ Δ → Val τ Δ

wk : ∀ {Γ Δ} → (∀ {σ} → Var σ Γ → Var σ Δ) → ∀ {σ} → Val σ Γ → Val σ Δ
wk ρ {base}    v = ren ρ v
wk ρ {arr σ τ} v = λ ρ′ → v (ρ′ ∘ ρ)

APP : ∀ {σ τ Γ} → Val (arr σ τ) Γ →  Val σ Γ → Val τ Γ
APP f t = f id t

LAM : ∀ {Γ σ τ} → Val (arr σ τ) Γ → Val (arr σ τ) Γ
LAM = id
\end{code}
%<*nbe>
\begin{code}
nbe : {Γ Δ : List Type} → (∀ {σ} → Var σ Γ → Val σ Δ) → (∀ {σ} → Tm σ Γ → Val σ Δ)
nbe ρ (`var v)    = ρ v
nbe ρ (f `$ t)  = APP (nbe ρ f) (nbe ρ t)
nbe ρ (`λ t)    = LAM (λ re v → nbe ((wk re ∘ ρ) -, v) t)
\end{code}
%</nbe>
\begin{code}
  where

  _-,_ : ∀ {Γ σ Δ} → (∀ {τ} → Var τ Γ → Val τ Δ) → Val σ Δ → ∀ {τ} → Var τ (σ ∷ Γ) → Val τ Δ
  (ρ -, v) ze     = v
  (ρ -, v) (su k) = ρ k
\end{code}


\begin{code}
open import Level
open import models as M

module Goal {𝓥 𝓒 : Model zero} (𝓢 : Semantics 𝓥 𝓒) where
\end{code}

%<*sem>
\begin{code}
 throwawaygoal : {Γ : Cx Ty} → [ (Γ -Env) 𝓥 ⟶ (Γ -Comp) 𝓒 ]
\end{code}
%</sem>
\begin{code}
 throwawaygoal = Eval.sem 𝓢
\end{code}
