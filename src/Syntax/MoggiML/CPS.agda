module Syntax.MoggiML.CPS where

open import Syntax         as λC
open import Syntax.MoggiML as ML
open import Semantics.Environment using (extend ; step)

CPS[_] : (r : λC.Type) (σ : ML.Type) → λC.Type
CPS[ r ] `Bool    = `Bool
CPS[ r ] `Unit    = `Unit
CPS[ r ] (σ `→ τ) = CPS[ r ] σ `→ CPS[ r ] τ
CPS[ r ] (# σ)    = (CPS[ r ] σ `→ r) `→ r

cps : ∀ {Γ σ r} → Γ ML.⊢ σ → CPS[ r ] <$> Γ λC.⊢ CPS[ r ] σ
cps (`var v)      = `var (map CPS[ _ ] v)
cps (f `$ t)      = cps f `$ cps t
cps (`λ t)        = `λ (cps t)
cps `⟨⟩           = `⟨⟩
cps `tt           = `tt
cps `ff           = `ff
cps (`ifte b l r) =
  `ifte (cps b) (cps l) (cps r)
cps (m `>>= f)    =
  let ⟦m⟧ = rename extend (cps m)
      ⟦f⟧ = rename (step extend) (cps f)
  in `λ (⟦m⟧ `$ `λ (⟦f⟧ `$ `var zero `$ `var (1+ zero)))
cps (`return t)   = `λ (`var zero `$ rename extend (cps t))
