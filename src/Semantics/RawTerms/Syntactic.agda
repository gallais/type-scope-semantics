module Semantics.RawTerms.Syntactic where

open import Data.Nat
open import Data.Fin
open import Function

open import Syntax.Type
open import Syntax.RawTerms
open import Semantics.RawTerms.Specification

REN : Semantics Fin Raw
Semantics.wk     REN = lookup
Semantics.embed  REN = id
Semantics.⟦var⟧  REN = `var
Semantics.⟦λ⟧    REN = λ σ b → `λ σ (b extend zero)
Semantics._⟦$⟧_  REN = _`$_
Semantics.⟦⟨⟩⟧   REN = `⟨⟩
Semantics.⟦tt⟧   REN = `tt
Semantics.⟦ff⟧   REN = `ff
Semantics.⟦ifte⟧ REN = `ifte

SUB : Semantics Raw Raw
Semantics.wk     SUB = Eval.sem REN
Semantics.embed  SUB = `var
Semantics.⟦var⟧  SUB = id
Semantics.⟦λ⟧    SUB = λ σ b → `λ σ (b extend (`var zero))
Semantics._⟦$⟧_  SUB = _`$_
Semantics.⟦⟨⟩⟧   SUB = `⟨⟩
Semantics.⟦tt⟧   SUB = `tt
Semantics.⟦ff⟧   SUB = `ff
Semantics.⟦ifte⟧ SUB = `ifte
