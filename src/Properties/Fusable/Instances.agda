module Properties.Fusable.Instances where

open import Syntax.Core hiding (_<$>_)
open import Syntax.Normal
open import Semantics.Environment as Env hiding (refl)
import Semantics.Specification
open import Semantics.Instances
open import Properties.Relation
open import Properties.Relation.Printing
open import Properties.Relation.βιξη
open import Properties.Synchronisable.Instances
open import Properties.Fusable.Specification
open import Properties.Fusable.Syntactic.Instances public
open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Product
open import Function as F
open import Relation.Binary.PropositionalEquality as PEq hiding (trans)

ifteRenNorm :
  ∀ {Γ Δ Θ σ} (b : Γ ⊢ `Bool) (l r : Γ ⊢ σ) → ∀ {ρ^A ρ^C} {ρ^B : Var Δ ⇒[ βιξη._⊨_ ] Θ} →
  related _≣_ (βιξη.eval (rename ρ^A b) ρ^B) (βιξη.eval b ρ^C) →
  related _≣_ (βιξη.eval (rename ρ^A l) ρ^B) (βιξη.eval l ρ^C) →
  related _≣_ (βιξη.eval (rename ρ^A r) ρ^B) (βιξη.eval r ρ^C) →
  related _≣_ (βιξη.eval (rename ρ^A (`ifte b l r)) ρ^B) (βιξη.eval (`ifte b l r) ρ^C)
ifteRenNorm b l r {ρ^A} {ρ^C} {ρ^B} eqB eqL eqR
  with βιξη.eval (rename ρ^A b) ρ^B | βιξη.eval b ρ^C
ifteRenNorm b l r refl eqL eqR | `neu pr ne | .(`neu pr ne) =
  reflect^≣ _ $ cong₂ (`ifte ne) (reify^≣ _ eqL) (reify^≣ _ eqR)
ifteRenNorm b l r refl eqL eqR | `tt       | .`tt         = eqL
ifteRenNorm b l r refl eqL eqR | `ff       | .`ff         = eqR

fusableRenamingNormalise :
  Fusable 𝓢^Renaming βιξη.Normalise βιξη.Normalise
  _≣_ (λ ρ^A ρ^B ρ^C → `∀[ _≣_ ] (trans ρ^A ρ^B) ρ^C) _≣_
fusableRenamingNormalise = record
  { reify^A = id
  ; 𝓔^R‿∙  = λ ρ^R u^R → lookup^R ρ^R ∙^R′ u^R
  ; 𝓔^R‿wk = λ inc ρ^R → pack^R $ wk^≣ inc ∘ lookup^R ρ^R
  ; R⟦var⟧  = λ v ρ^R → lookup^R ρ^R v
  ; R⟦λ⟧    = λ b ρ^R r → r
  ; R⟦$⟧    = λ f t ρ^R F T → F Env.refl T
  ; R⟦⟨⟩⟧   = const _
  ; R⟦tt⟧   = const PEq.refl
  ; R⟦ff⟧   = const PEq.refl
  ; R⟦ifte⟧ = λ b l r _ → ifteRenNorm b l r
  }

fuseRenamingEvaluate :
  ∀ {Γ Δ Θ σ} (t : Γ ⊢ σ) (inc : Renaming Γ Δ) (ρ : Var Δ ⇒[ βιξη._⊨_ ] Θ) →
  `∀[ _≣_ ] ρ ρ →
  EQREL Θ σ (βιξη.eval (rename inc t) ρ) (βιξη.eval t (trans inc ρ))
fuseRenamingEvaluate t inc ρ ρ^R =
  Fundamental.lemma fusableRenamingNormalise t $ pack^R $ lookup^R ρ^R ∘ lookup inc
  
fuseRenamingNormalise :
  ∀ {Γ Δ σ} (t : Γ ⊢ σ) (inc : Renaming Γ Δ) →
  βιξη.norm' (rename inc t) ≡
  βιξη.reify _ (βιξη.eval t ((βιξη.reflect _ ∘ `var) <$> inc))
fuseRenamingNormalise t inc =
  reify^≣ _ $ Fundamental.lemma fusableRenamingNormalise t
            $ pack^R $ λ v → reflect^≣ _ PEq.refl

ifteSubNorm :
  ∀ {Γ Δ Θ σ} (b : Γ ⊢ `Bool) (l r : Γ ⊢ σ) → ∀ {ρ^A ρ^C} {ρ^B : Var Δ ⇒[ βιξη._⊨_ ] Θ} →
  related _≣_ (βιξη.eval (substitute b ρ^A) ρ^B) (βιξη.eval b ρ^C) →
  related _≣_ (βιξη.eval (substitute l ρ^A) ρ^B) (βιξη.eval l ρ^C) →
  related _≣_ (βιξη.eval (substitute r ρ^A) ρ^B) (βιξη.eval r ρ^C) →
  related _≣_ (βιξη.eval (substitute (`ifte b l r) ρ^A) ρ^B) (βιξη.eval (`ifte b l r) ρ^C)
ifteSubNorm b l r {ρ^A} {ρ^C} {ρ^B} eqB eqL eqR
  with βιξη.eval (substitute b ρ^A) ρ^B | βιξη.eval b ρ^C
ifteSubNorm b l r refl eqL eqR | `neu pr ne | .(`neu pr ne) =
  reflect^≣ _ $ cong₂ (`ifte ne) (reify^≣ _ eqL) (reify^≣ _ eqR)
ifteSubNorm b l r refl eqL eqR | `tt       | .`tt         = eqL
ifteSubNorm b l r refl eqL eqR | `ff       | .`ff         = eqR

fusableSubstitutionNormalise :
  Fusable 𝓢^Substitution βιξη.Normalise βιξη.Normalise
  _≣_ (λ ρ^A ρ^B ρ^C → `∀[ _≣_ ] ρ^B ρ^B
      × (∀ {Ω} (inc : Renaming _ Ω) →
         `∀[ _≣_ ] (flip βιξη.eval (βιξη.wk^⊨ inc <$> ρ^B) <$> ρ^A) (βιξη.wk^⊨ inc <$> ρ^C))
      ×  `∀[ _≣_ ] (flip βιξη.eval ρ^B <$> ρ^A) ρ^C)
  _≣_
fusableSubstitutionNormalise = record
  { reify^A = id
  ; 𝓔^R‿∙  = λ {_ _ _ _ ρ^A ρ^B ρ^C} ρ^R u^R →
             let (ρ^R₁ , ρ^R₂ , ρ^R₃) = ρ^R
                 ρ^R₁′ = ρ^R₁ ∙^R refl≣ u^R
             in ρ^R₁′
             , (λ inc →
               let ρ^R′ = λ {σ} (v : σ ∈ _) →
                          let env^R = pack^R $ λ v → wk^≣ inc (lookup^R ρ^R₁′ v)
                          in trans≣ (fuseRenamingEvaluate (lookup ρ^A v) extend _ env^R)
                                    (lookup^R (ρ^R₂ inc) v)
               in ρ^R′ ∙^R′ wk^≣ inc u^R)
             , let ρ^R′ = λ {σ} (v : σ ∈ _) →
                          trans≣ (fuseRenamingEvaluate (lookup ρ^A v) extend _ ρ^R₁′)
                                 (lookup^R ρ^R₃ v)
               in ρ^R′ ∙^R′ u^R
  ; 𝓔^R‿wk = λ {Γ Δ Θ} inc {ρ^A ρ^B ρ^C} ρ^R →
             let (ρ^R₁ , ρ^R₂ , ρ^R₃) = ρ^R
             in (pack^R $ λ v → wk^≣ inc $ lookup^R ρ^R₁ v)
             , (λ {Ω} inc′ →
                let INC : Renaming Θ Ω
                    INC = Env.trans inc inc′
                    wkρ^B : Var Δ ⇒[ βιξη._⊨_ ] Ω
                    -- for some reason using <$> breaks inference
                    wkρ^B = pack $ λ v → βιξη.wk^⊨ inc′ $ βιξη.wk^⊨ inc $ lookup ρ^B v
                    ρ^R′ : `∀[ _≣_ ] wkρ^B (βιξη.wk^⊨ INC <$> ρ^B)
                    ρ^R′ = pack^R $ λ v → wk^⊨-trans inc inc′ (lookup^R ρ^R₁ v)
                in pack^R $ λ v →
                trans≣ (refl^βιξη (lookup ρ^A v) ρ^R′)
                $ trans≣ (lookup^R (ρ^R₂ INC) v)
                $ sym≣ $ wk^⊨-trans inc inc′ $ refl≣ $ sym≣ $ lookup^R ρ^R₃ v)
             , ρ^R₂ inc
  ; R⟦var⟧  = λ v ρ^R → lookup^R (proj₂ ∘ proj₂ $ ρ^R) v
  ; R⟦λ⟧    = λ _ _ r → r
  ; R⟦$⟧    = λ _ _ _ r → r Env.refl
  ; R⟦⟨⟩⟧   = λ _ → _
  ; R⟦tt⟧   = const PEq.refl
  ; R⟦ff⟧   = const PEq.refl
  ; R⟦ifte⟧ = λ b l r _ → ifteSubNorm b l r
  }

open import Codata.Thunk
open import Codata.Stream

fusableRenamingPrinting :
  Fusable 𝓢^Renaming Printing Printing
  Equality (λ ρ^A ρ^B → `∀[ Equality ] (trans ρ^A ρ^B)) _≈_
fusableRenamingPrinting = record
  { reify^A = id
  ; 𝓔^R‿∙   = λ ρ^R eq → lookup^R ρ^R ∙^R′ eq
  ; 𝓔^R‿wk  = λ inc ρ^R → pack^R $ λ v → cong (mkName ∘ runName) $ lookup^R ρ^R v
  ; R⟦var⟧  = λ v ρ^R → cong₂ (_,_ ∘ runName) (lookup^R ρ^R v)
  ; R⟦λ⟧    = λ {_ _ Θ σ} t ρ^R r → λ { {n₁ ∷ n₁s} {n₂ ∷ n₂s} eq →
              let (neq , nseq)   = ∷-inj eq
                  inc : Renaming Θ (Θ ∙ σ)
                  inc = extend
                  (ihstr , ihns) = ,-inj (r inc (cong mkName neq) nseq)
              in cong₂ _,_ (cong₂ formatλ neq ihstr) ihns}
  ; R⟦$⟧    = λ _ _ _ ihf iht eq →
              let (ihstrf , eq₁) = ,-inj (ihf eq)
                  (ihstrt , eq₂) = ,-inj (iht eq₁)
              in cong₂ _,_ (cong₂ format$ ihstrf ihstrt) eq₂
  ; R⟦⟨⟩⟧   = λ _ → cong _
  ; R⟦tt⟧   = λ _ → cong _
  ; R⟦ff⟧   = λ _ → cong _
  ; R⟦ifte⟧ = λ _ _ _ _ ihb ihl ihr eq →
              let (ihstrb , eq₁) = ,-inj (ihb eq)
                  (ihstrl , eq₂) = ,-inj (ihl eq₁)
                  (ihstrr , eq₃) = ,-inj (ihr eq₂)
              in cong₂ _,_ (cong₂ (uncurry formatIf) (cong₂ _,_ ihstrb ihstrl) ihstrr) eq₃
  } where


  ∷-inj : ∀ {A a b as bs} → (Stream A _ F.∋ a ∷ as) ≡ b ∷ bs →
          a ≡ b × as .force ≡ bs .force
  ∷-inj refl = PEq.refl , refl

  ,-inj : {A B : Set} {a c : A} {b d : B} → (a , b) ≡ (c , d) → a ≡ c × b ≡ d
  ,-inj refl = PEq.refl , refl

-- currently missing from the stdlib
drop : ∀ {a} {A : Set a} → ℕ → Stream A _ → Stream A _
drop zero    xs = xs
drop (suc n) xs = drop n (tail xs)

fuseRenamingPrinting :
  ∀ {Γ σ} (t : ε ⊢ σ) (inc : Renaming ε Γ) →
  print (rename inc t)
  ≡ proj₁ (runPrinter (printer t (Var ε ⇒[ Name ] Γ F.∋ `ε)) $ drop (size Γ) names)
fuseRenamingPrinting {Γ} t inc =
  cong proj₁ (Fundamental.lemma fusableRenamingPrinting t (pack^R $ λ ()) $ proof Γ Γ)

  where

    tail-init : ∀ Γ Δ {ns} → tail (proj₂ (init Γ Δ ns)) ≡ proj₂ (init Γ Δ (tail ns))
    tail-init ε       Δ = refl
    tail-init (Γ ∙ _) Δ = cong tail $ tail-init Γ Δ

    proof : ∀ Γ Δ {names} → proj₂ (init Γ Δ names) ≡ drop (size Γ) names
    proof ε       Δ         = refl
    proof (Γ ∙ _) Δ {_ ∷ _} = PEq.trans (tail-init Γ Δ) (proof Γ Δ)
