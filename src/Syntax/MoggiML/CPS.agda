module Syntax.MoggiML.CPS where

open import Syntax         as λC
open import Syntax.MoggiML as ML
open import Semantics.Environment using (extend ; step)
open import Semantics.Syntactic.Instances using (rename)

-- The continuation monad
Cont : λC.Type → λC.Type → λC.Type
Cont r σ = (σ `→ r) `→ r

return : ∀ {Γ σ r} → Γ λC.⊢ σ → Γ λC.⊢ Cont r σ
return t = `λ (`var zero `$ rename extend t)

bind : ∀ {Γ σ τ r} → Γ λC.⊢ Cont r σ → Γ λC.⊢ (σ `→ Cont r τ) → Γ λC.⊢ Cont r τ
bind m f = `λ {- k -} (rename extend m `$ `λ {- v:σ -}
           ((rename (step extend) f `$ `var zero) `$ `var (1+ zero)))

-- Translation of ML types using the continuation monad to interpret the
-- computational monad #_

CPS[_]  : (r : λC.Type) (σ : ML.Type) → λC.Type
#CPS[_] : (r : λC.Type) (σ : ML.Type) → λC.Type

CPS[ r ] `Bool     = `Bool
CPS[ r ] `Unit     = `Unit
CPS[ r ] (σ `→# τ) = CPS[ r ] σ `→ #CPS[ r ] τ
CPS[ r ] (# σ)     = #CPS[ r ] σ

#CPS[ r ] σ = Cont r (CPS[ r ] σ)

-- From terms in moggi's ML to terms in the λC via the CPS monad

cps : ∀ {Γ σ r} → Γ ML.⊢ σ → CPS[ r ] <$> Γ λC.⊢ CPS[ r ] σ
cps (`var v)      = `var (map CPS[ _ ] v)
cps (f `$ t)      = cps f `$ cps t
cps (`λ t)        = `λ (cps t)
cps `⟨⟩           = `⟨⟩
cps `tt           = `tt
cps `ff           = `ff
cps (`ifte b l r) = `ifte (cps b) (cps l) (cps r)
cps (m `>>= f)    = bind (cps m) (cps f)
cps (`return t)   = return (cps t)
