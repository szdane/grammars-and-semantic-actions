{-# OPTIONS --allow-unsolved-metas #-}
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module Metatheory.Simple.StringToContext (Σ₀ : hSet ℓ-zero) where

open import Cubical.Foundations.Structure
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Data.Empty hiding (⊥)
open import Cubical.Data.Sigma
open import Cubical.Data.Sum
open import Cubical.Data.List as List hiding ([_])
open import Cubical.Data.FinData
open import Cubical.Data.Unit

open import String.Base Σ₀
open import Metatheory.Simple.Syntax Σ₀

-- In this file we construct a strong monoidal functor (of groupoids)
-- from ΔΣ* to Ctx,Subst

⌈_⌉ : String → Ctx
⌈ w ⌉ = List.rec εc (λ c ⌈w'⌉ → ty (lit c) ⊗c ⌈w'⌉) w

⌈ε⌉ : εc ≡ ⌈ [] ⌉
⌈ε⌉ = refl

⌈++⌉ : ∀ w1 w2 → ⌈ w1 ⌉ ⊗c ⌈ w2 ⌉ ≡ ⌈ w1 ++ w2 ⌉
⌈++⌉ [] w2 = εc⊗c
⌈++⌉ (c ∷ w1) w2 = ⊗c⊗c ∙ cong (ty (lit c) ⊗c_) (⌈++⌉ w1 w2)

-- The three laws of strong monoidal functors can all be stated here in terms of paths
str-mon-unit-l : ∀ w → Path (εc ⊗c ⌈ w ⌉ ≡ ⌈ w ⌉) εc⊗c (⌈++⌉ [] w)
str-mon-unit-l w = refl

str-mon-unit-r : ∀ w → Path (⌈ w ⌉ ⊗c εc ≡  ⌈ w ⌉) ⊗cεc (⌈++⌉ w [] ∙ cong ⌈_⌉ (++-unit-r w))
str-mon-unit-r [] = λ≡ρ ∙ rUnit εc⊗c
str-mon-unit-r (c ∷ w) =
  ⊗cεc
    ≡⟨ mon-lem' (ty (lit c)) ⌈ w ⌉ ⟩
  (⊗c⊗c ∙ cong (ty (lit c) ⊗c_) ⊗cεc)
    ≡⟨ cong (⊗c⊗c ∙_) (cong (cong (ty (lit c) ⊗c_)) (str-mon-unit-r w)) ⟩
  (⊗c⊗c ∙ (cong (ty (lit c) ⊗c_) ((⌈++⌉ w [] ∙ cong ⌈_⌉ (++-unit-r w)))))
    ≡⟨ (λ i → ⊗c⊗c ∙ cong-∙ (ty (lit c) ⊗c_) (⌈++⌉ w []) (cong ⌈_⌉ (++-unit-r w)) i) ⟩
  (⊗c⊗c ∙ (cong (ty (lit c) ⊗c_) (⌈++⌉ w []) ∙ cong (ty (lit c) ⊗c_) (cong ⌈_⌉ (++-unit-r w))))
    ≡⟨ assoc _ _ _ ⟩
  ((⊗c⊗c ∙ cong (ty (lit c) ⊗c_) (⌈++⌉ w [])) ∙ cong (ty (lit c) ⊗c_) (cong ⌈_⌉ (++-unit-r w)))
  ∎

str-mon-assoc : ∀ w1 w2 w3
  → Path ((⌈ w1 ⌉ ⊗c ⌈ w2 ⌉) ⊗c ⌈ w3 ⌉ ≡ ⌈ w1 ++ (w2 ++ w3) ⌉)
         ((λ i → ⌈++⌉ w1 w2 i ⊗c ⌈ w3 ⌉) ∙ ⌈++⌉ (w1 ++ w2) w3 ∙ cong ⌈_⌉ (++-assoc w1 w2 w3))
         (⊗c⊗c ∙ (λ i → ⌈ w1 ⌉ ⊗c ⌈++⌉ w2 w3 i) ∙ ⌈++⌉ w1 (w2 ++ w3))
str-mon-assoc [] w2 w3 = {!!}
str-mon-assoc (c ∷ w1) w2 w3 = {!!}

opaque
  ⌈ε⌉-subst : Subst ⌈ [] ⌉ εc
  ⌈ε⌉-subst = ids

  ⌈++⌉-subst : ∀ w1 w2 → Subst ⌈ w1 ++ w2 ⌉ (⌈ w1 ⌉ ⊗c ⌈ w2 ⌉)
  ⌈++⌉-subst w1 w2 = subst (λ w1w2 → Subst w1w2 (⌈ w1 ⌉ ⊗c ⌈ w2 ⌉)) (⌈++⌉ w1 w2) ids

