\begin{code}
module motivation where

open import Data.List
open import Function

data Type : Set where
  Base : Type
  Arr  : Type → Type → Type

data Id : List Type → Type → Set where
  zero : ∀ {Γ σ} → Id (σ ∷ Γ) σ
  suc  : ∀ {Γ σ τ} → Id Γ σ → Id (τ ∷ Γ) σ

_⇒_ : {A : Set} → (A → Set) → (A → Set) → Set
f ⇒ g = ∀ {a} → f a → g a

data Tm (Γ : List Type) : Type → Set where
  Var : ∀ {σ} → Id Γ σ → Tm Γ σ
  App : ∀ {σ τ} → Tm Γ (Arr σ τ) → Tm Γ σ → Tm Γ τ
  Lam : ∀ {σ τ} → Tm (σ ∷ Γ) τ → Tm Γ (Arr σ τ)
\end{code}
%<*ren>
\begin{code}
ren : ∀ {Γ Δ} → (Id Γ ⇒  Id Δ) → Tm Γ ⇒ Tm Δ
ren ρ (Var v)    = Var (ρ v)
ren ρ (App f t)  = App (ren ρ f) (ren ρ t)
ren ρ (Lam b)    = Lam (ren ((suc ∘ ρ) ∙ zero) b)
\end{code}
%</ren>
\begin{code}
  where 

  _∙_ : ∀ {Γ Δ σ} → (Id Γ ⇒ Id Δ) → Id Δ σ → Id (σ ∷ Γ) ⇒ Id Δ
  (ρ ∙ v) zero    = v
  (ρ ∙ v) (suc k) = ρ k
\end{code}
%<*sub>
\begin{code}
sub : ∀ {Γ Δ} → (Id Γ ⇒ Tm Δ) → Tm Γ ⇒ Tm Δ
sub ρ (Var v)    = ρ v
sub ρ (App f t)  = App (sub ρ f) (sub ρ t)
sub ρ (Lam b)    = Lam (sub ((ren suc ∘ ρ) ∙ Var zero) b)
\end{code}
%</sub>
\begin{code}
  where

  _∙_ :  ∀ {Γ Δ σ} → (Id Γ ⇒ Tm Δ) → Tm Δ σ → Id (σ ∷ Γ) ⇒ Tm Δ
  (ρ ∙ v) zero    = v
  (ρ ∙ v) (suc k) = ρ k

record Kit (◆ : List Type → Type → Set) : Set where
  field
    var : ∀ {Γ} → ◆ Γ ⇒ Tm Γ
    zro : ∀ {Γ σ} → ◆ (σ ∷ Γ) σ
    wkn : ∀ {Γ σ} → ◆ Γ ⇒ ◆ (σ ∷ Γ)
\end{code}
%<*kit>
\begin{code}
kit : ∀ {Γ Δ ◆} → Kit ◆ → (Id Γ ⇒ ◆ Δ) → Tm Γ ⇒ Tm Δ
kit κ ρ (Var v)    = Kit.var κ (ρ v)
kit κ ρ (App f t)  = App (kit κ ρ f) (kit κ ρ t)
kit κ ρ (Lam b)    = Lam (kit κ ((Kit.wkn κ ∘ ρ) ∙ Kit.zro κ) b)
\end{code}
%</kit>
\begin{code}
  where

  help : ∀ {◆} → Kit ◆ → List Type → Type → Set
  help {◆} _ = ◆

  ◆ = help κ

  _∙_ :  ∀ {Γ Δ σ} → (Id Γ ⇒ ◆ Δ) → ◆ Δ σ → Id (σ ∷ Γ) ⇒ ◆ Δ
  (ρ ∙ v) zero    = v
  (ρ ∙ v) (suc k) = ρ k

Val : List Type → Type → Set
Val Γ Base      = Tm Γ Base
Val Γ (Arr σ τ) = ∀ {Δ} → (Id Γ ⇒ Id Δ) → Val Δ σ → Val Δ τ

wk : ∀ {Γ Δ} → (Id Γ ⇒ Id Δ) → Val Γ ⇒ Val Δ
wk ρ {Base}    v = ren ρ v
wk ρ {Arr σ τ} v = λ ρ′ → v (ρ′ ∘ ρ)

APP : ∀ {Γ σ τ} → Val Γ (Arr σ τ) → Val Γ σ → Val Γ τ
APP f t = f id t

LAM : ∀ {Γ σ τ} → Val Γ (Arr σ τ) → Val Γ (Arr σ τ)
LAM = id
\end{code}
%<*nbe>
\begin{code}
nbe : ∀ {Γ Δ} → (Id Γ ⇒ Val Δ) → Tm Γ ⇒ Val Δ
nbe ρ (Var v)    = ρ v
nbe ρ (App f t)  = APP (nbe ρ f) (nbe ρ t)
nbe ρ (Lam t)    = LAM (λ re v → nbe ((wk re ∘ ρ) ∙ v) t)
\end{code}
%</nbe>
\begin{code}
  where

  _∙_ : ∀ {Γ Δ σ} → (Id Γ ⇒ Val Δ) → Val Δ σ → Id (σ ∷ Γ) ⇒ Val Δ
  (ρ ∙ v) zero    = v
  (ρ ∙ v) (suc k) = ρ k
\end{code}
