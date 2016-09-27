\begin{code}
module motivation where

open import Data.List
open import Function

data Type : Set where
  Base : Type
  Arr  : Type → Type → Type

data Var : List Type → Type → Set where
  Z : ∀ {Γ σ} → Var (σ ∷ Γ) σ
  S : ∀ {Γ σ τ} → Var Γ σ → Var (τ ∷ Γ) σ

_⇒_ : {A : Set} → (A → Set) → (A → Set) → Set
f ⇒ g = ∀ {a} → f a → g a

data Tm (Γ : List Type) : Type → Set where
  `var : ∀ {σ} → Var Γ σ → Tm Γ σ
  _`$_ : ∀ {σ τ} → Tm Γ (Arr σ τ) → Tm Γ σ → Tm Γ τ
  `λ   : ∀ {σ τ} → Tm (σ ∷ Γ) τ → Tm Γ (Arr σ τ)
\end{code}
%<*ren>
\begin{code}
ren : {Γ Δ : List Type} → (Var Γ ⇒  Var Δ) → Tm Γ ⇒ Tm Δ
ren ρ (`var v)  = `var (ρ v)
ren ρ (f `$ t)  = ren ρ f `$ ren ρ t
ren ρ (`λ b)    = `λ (ren ((S ∘ ρ) -, Z) b)
\end{code}
%</ren>
\begin{code}
  where 

  _-,_ : ∀ {Γ Δ σ} → (Var Γ ⇒ Var Δ) → Var Δ σ → Var (σ ∷ Γ) ⇒ Var Δ
  (ρ -, v) Z     = v
  (ρ -, v) (S k) = ρ k
\end{code}
%<*sub>
\begin{code}
sub : {Γ Δ : List Type} → (Var Γ ⇒ Tm Δ) → Tm Γ ⇒ Tm Δ
sub ρ (`var v)  = ρ v
sub ρ (f `$ t)  = sub ρ f `$ sub ρ t
sub ρ (`λ b)    = `λ (sub ((ren S ∘ ρ) -, `var Z) b)
\end{code}
%</sub>
\begin{code}
  where

  _-,_ :  ∀ {Γ Δ σ} → (Var Γ ⇒ Tm Δ) → Tm Δ σ → Var (σ ∷ Γ) ⇒ Tm Δ
  (ρ -, v) Z     = v
  (ρ -, v) (S k) = ρ k

record Kit (◆ : List Type → Type → Set) : Set where
  field
    var : ∀ {Γ} → ◆ Γ ⇒ Tm Γ
    zro : ∀ {Γ σ} → ◆ (σ ∷ Γ) σ
    wkn : ∀ {Γ σ} → ◆ Γ ⇒ ◆ (σ ∷ Γ)
\end{code}
%<*kit>
\begin{code}
kit : {Γ Δ : List Type} {◆ : List Type → Type → Set} → Kit ◆ → (Var Γ ⇒ ◆ Δ) → Tm Γ ⇒ Tm Δ
kit κ ρ (`var v)  = Kit.var κ (ρ v)
kit κ ρ (f `$ t)  = kit κ ρ f `$ kit κ ρ t
kit κ ρ (`λ b)    = `λ (kit κ ((Kit.wkn κ ∘ ρ) -, Kit.zro κ) b)
\end{code}
%</kit>
\begin{code}
  where

  help : ∀ {◆} → Kit ◆ → List Type → Type → Set
  help {◆} _ = ◆

  ◆ = help κ

  _-,_ :  ∀ {Γ Δ σ} → (Var Γ ⇒ ◆ Δ) → ◆ Δ σ → Var (σ ∷ Γ) ⇒ ◆ Δ
  (ρ -, v) Z    = v
  (ρ -, v) (S k) = ρ k

Val : List Type → Type → Set
Val Γ Base      = Tm Γ Base
Val Γ (Arr σ τ) = ∀ {Δ} → (Var Γ ⇒ Var Δ) → Val Δ σ → Val Δ τ

wk : ∀ {Γ Δ} → (Var Γ ⇒ Var Δ) → Val Γ ⇒ Val Δ
wk ρ {Base}    v = ren ρ v
wk ρ {Arr σ τ} v = λ ρ′ → v (ρ′ ∘ ρ)

APP : ∀ {Γ σ τ} → Val Γ (Arr σ τ) → Val Γ σ → Val Γ τ
APP f t = f id t

LAM : ∀ {Γ σ τ} → Val Γ (Arr σ τ) → Val Γ (Arr σ τ)
LAM = id
\end{code}
%<*nbe>
\begin{code}
nbe : {Γ Δ : List Type} → (Var Γ ⇒ Val Δ) → Tm Γ ⇒ Val Δ
nbe ρ (`var v)    = ρ v
nbe ρ (f `$ t)  = APP (nbe ρ f) (nbe ρ t)
nbe ρ (`λ t)    = LAM (λ re v → nbe ((wk re ∘ ρ) -, v) t)
\end{code}
%</nbe>
\begin{code}
  where

  _-,_ : ∀ {Γ Δ σ} → (Var Γ ⇒ Val Δ) → Val Δ σ → Var (σ ∷ Γ) ⇒ Val Δ
  (ρ -, v) Z     = v
  (ρ -, v) (S k) = ρ k
\end{code}
