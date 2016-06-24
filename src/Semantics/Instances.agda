module Semantics.Instances where

open import Semantics.Syntactic.Renaming                              public
open import Semantics.Syntactic.Substitution                          public
open import Semantics.NormalisationByEvaluation.βιξη
open import Semantics.NormalisationByEvaluation.βιξ
open import Semantics.NormalisationByEvaluation.βι

module βιξη = Semantics.NormalisationByEvaluation.βιξη
module βιξ  = Semantics.NormalisationByEvaluation.βιξ
module βι   = Semantics.NormalisationByEvaluation.βι
