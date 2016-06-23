module README where

-- Basic syntax
open import Syntax.Type
open import Syntax.Context
open import Syntax.Calculus

open import Syntax.Core.Examples

-- Abstract presentation of the notion of Model
open import Semantics.Model
open import Semantics.Environment
open import Semantics.Specification

-- Syntactic Models are very simple Models
open import Semantics.Syntactic.Specification
open import Semantics.Syntactic.Renaming
open import Semantics.Syntactic.Substitution

-- Monadic Model
open import Semantics.Printing

-- Normalisation by Evaluation goes through a Model
open import Syntax.Normal
open import Semantics.NormalisationByEvaluation.βιξη
open import Semantics.NormalisationByEvaluation.βιξ
open import Semantics.NormalisationByEvaluation.βι

open import Semantics.Examples
