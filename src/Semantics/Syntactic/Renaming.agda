module Semantics.Syntactic.Renaming where

open import Syntax.Core
open import Semantics.Environment
open import Semantics.Syntactic.Specification

SyntacticRenaming : Syntactic _∋_
SyntacticRenaming = record { embed = refl ; wk = wk^∋ ; ⟦var⟧ = `var }

𝓢^Renaming = Fundamental.syntactic SyntacticRenaming 

rename : Weakening _⊢_
rename ren t = Fundamental.lemma SyntacticRenaming t ren
