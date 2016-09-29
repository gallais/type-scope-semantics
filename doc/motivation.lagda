\begin{code}
module motivation where

open import Data.List
open import Function

data Type : Set where
  base : Type
  arr  : Type → Type → Type

data Var : List Type → Type → Set where
  ze : ∀ {Γ σ} → Var (σ ∷ Γ) σ
  su : ∀ {Γ σ τ} → Var Γ σ → Var (τ ∷ Γ) σ

_⇒_ : {A : Set} → (A → Set) → (A → Set) → Set
f ⇒ g = ∀ {a} → f a → g a

data Tm (Γ : List Type) : Type → Set where
  `var : ∀ {σ} → Var Γ σ → Tm Γ σ
  _`$_ : ∀ {σ τ} → Tm Γ (arr σ τ) → Tm Γ σ → Tm Γ τ
  `λ   : ∀ {σ τ} → Tm (σ ∷ Γ) τ → Tm Γ (arr σ τ)
\end{code}
%<*ren>
\begin{code}
ren : {Γ Δ : List Type} → (∀ {σ} → Var Γ σ → Var Δ σ) → (∀ {σ} → Tm Γ σ → Tm Δ σ)
ren ρ (`var v)  = `var (ρ v)
ren ρ (f `$ t)  = ren ρ f `$ ren ρ t
ren ρ (`λ b)    = `λ (ren ((su ∘ ρ) -, ze) b)
\end{code}
%</ren>
\begin{code}
  where 

  _-,_ : ∀ {Γ Δ σ} → (Var Γ ⇒ Var Δ) → Var Δ σ → Var (σ ∷ Γ) ⇒ Var Δ
  (ρ -, v) ze     = v
  (ρ -, v) (su k) = ρ k
\end{code}
%<*sub>
\begin{code}
sub : {Γ Δ : List Type} → (∀ {σ} → Var Γ σ → Tm Δ σ) → (∀ {σ} → Tm Γ σ → Tm Δ σ)
sub ρ (`var v)  = ρ v
sub ρ (f `$ t)  = sub ρ f `$ sub ρ t
sub ρ (`λ b)    = `λ (sub ((ren su ∘ ρ) -, `var ze) b)
\end{code}
%</sub>
\begin{code}
  where

  _-,_ :  ∀ {Γ Δ σ} → (Var Γ ⇒ Tm Δ) → Tm Δ σ → Var (σ ∷ Γ) ⇒ Tm Δ
  (ρ -, v) ze     = v
  (ρ -, v) (su k) = ρ k

record Kit (◆ : List Type → Type → Set) : Set where
  field
    var : ∀ {Γ} → ◆ Γ ⇒ Tm Γ
    zro : ∀ {Γ σ} → ◆ (σ ∷ Γ) σ
    wkn : ∀ {Γ σ} → ◆ Γ ⇒ ◆ (σ ∷ Γ)

module kitkit {◆ : List Type → Type → Set} (κ : Kit ◆) where
\end{code}
%<*kit>
\begin{code}
  kit : {Γ Δ : List Type} → (∀ {σ} → Var Γ σ → ◆ Δ σ) → (∀ {σ} → Tm Γ σ → Tm Δ σ)
  kit ρ (`var v)  = Kit.var κ (ρ v)
  kit ρ (f `$ t)  = kit ρ f `$ kit ρ t
  kit ρ (`λ b)    = `λ (kit ((Kit.wkn κ ∘ ρ) -, Kit.zro κ) b)
\end{code}
%</kit>
\begin{code}
    where

    _-,_ :  ∀ {Γ Δ σ} → (Var Γ ⇒ ◆ Δ) → ◆ Δ σ → Var (σ ∷ Γ) ⇒ ◆ Δ
    (ρ -, v) ze    = v
    (ρ -, v) (su k) = ρ k

Val : List Type → Type → Set
Val Γ base      = Tm Γ base
Val Γ (arr σ τ) = ∀ {Δ} → (Var Γ ⇒ Var Δ) → Val Δ σ → Val Δ τ

wk : ∀ {Γ Δ} → (Var Γ ⇒ Var Δ) → Val Γ ⇒ Val Δ
wk ρ {base}    v = ren ρ v
wk ρ {arr σ τ} v = λ ρ′ → v (ρ′ ∘ ρ)

APP : ∀ {Γ σ τ} → Val Γ (arr σ τ) → Val Γ σ → Val Γ τ
APP f t = f id t

LAM : ∀ {Γ σ τ} → Val Γ (arr σ τ) → Val Γ (arr σ τ)
LAM = id
\end{code}
%<*nbe>
\begin{code}
nbe : {Γ Δ : List Type} → (∀ {σ} → Var Γ σ → Val Δ σ) → (∀ {σ} → Tm Γ σ → Val Δ σ)
nbe ρ (`var v)    = ρ v
nbe ρ (f `$ t)  = APP (nbe ρ f) (nbe ρ t)
nbe ρ (`λ t)    = LAM (λ re v → nbe ((wk re ∘ ρ) -, v) t)
\end{code}
%</nbe>
\begin{code}
  where

  _-,_ : ∀ {Γ Δ σ} → (Var Γ ⇒ Val Δ) → Val Δ σ → Var (σ ∷ Γ) ⇒ Val Δ
  (ρ -, v) ze     = v
  (ρ -, v) (su k) = ρ k
\end{code}
