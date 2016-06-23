module Syntax.Normal.Weakening where

open import Syntax.Type
open import Syntax.Normal
open import Semantics.Environment
open import Semantics.Syntactic.Renaming

mutual

  wk^ne : {R : Type → Set} → Weakening (_⊢[ R ]^ne_)
  wk^ne inc (`var v)        = `var (wk^∋ inc v)
  wk^ne inc (ne `$ u)       = wk^ne inc ne `$ wk^nf inc u
  wk^ne inc (`ifte ne l r)  = `ifte (wk^ne inc ne) (wk^nf inc l) (wk^nf inc r)

  wk^nf : {R : Type → Set} → Weakening (_⊢[ R ]^nf_)
  wk^nf inc (`neu pr t) = `neu pr (wk^ne inc t)
  wk^nf inc `⟨⟩         = `⟨⟩
  wk^nf inc `tt         = `tt
  wk^nf inc `ff         = `ff
  wk^nf inc (`λ nf)     = `λ (wk^nf (pop! inc) nf)

wk^whne : Weakening _⊢^whne_
wk^whne inc (`var v)        = `var (wk^∋ inc v)
wk^whne inc (ne `$ u)       = wk^whne inc ne `$ rename inc u
wk^whne inc (`ifte ne l r)  = `ifte (wk^whne inc ne) (rename inc l) (rename inc r)

wk^whnf : Weakening _⊢^whnf_
wk^whnf inc (`whne t)  = `whne (wk^whne inc t)
wk^whnf inc `⟨⟩        = `⟨⟩
wk^whnf inc `tt        = `tt
wk^whnf inc `ff        = `ff
wk^whnf inc (`λ b)     = `λ (rename (pop! inc) b)
