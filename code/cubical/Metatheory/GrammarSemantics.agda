{-# OPTIONS -WnoUnsupportedIndexedMatch #-}
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module Metatheory.GrammarSemantics (Σ₀ : hSet ℓ-zero) where

open import Cubical.Foundations.Structure
open import Cubical.Foundations.Univalence
open import Cubical.Data.Empty hiding (⊥)
open import Cubical.Data.Sigma
open import Cubical.Data.Bool hiding (_⊕_)
open import Cubical.Data.Sum
open import Cubical.Data.FinData
open import Cubical.Data.Unit

import Metatheory.Syntax Σ₀ as Syntax
open import Grammar Σ₀
open import Grammar.KleeneStar Σ₀
open import Grammar.Equivalence Σ₀
open import Term Σ₀

⟦_⟧ctx : Syntax.Ctx → Type ℓ-zero
⟦_⟧subst : ∀ {Δ Δ'} → Syntax.Subst Δ Δ' → ⟦ Δ ⟧ctx → ⟦ Δ' ⟧ctx
⟦_⟧ty : ∀ {Δ} → Syntax.Ty Δ → ⟦ Δ ⟧ctx → Type ℓ-zero
⟦_⟧tm : ∀ {Δ A} → Syntax.Tm Δ A → ∀ (δ : ⟦ Δ ⟧ctx) → ⟦ A ⟧ty δ

⟦_⟧gctx : ∀ {Δ} → Syntax.GCtx Δ → ⟦ Δ ⟧ctx → Grammar ℓ-zero
⟦_⟧gty  : ∀ {Δ} → Syntax.GTy Δ → ⟦ Δ ⟧ctx → Grammar ℓ-zero
⟦_⟧gsubst : ∀ {Δ Γ Γ'} → Syntax.GSubst Γ Γ' → (δ : ⟦ Δ ⟧ctx) → ⟦ Γ ⟧gctx δ ⊢ ⟦ Γ' ⟧gctx δ
⟦_⟧gtm : ∀ {Δ Γ A} → Syntax.GTm Γ A → (δ : ⟦ Δ ⟧ctx) → ⟦ Γ ⟧gctx δ ⊢ ⟦ A ⟧gty δ

⟦ Syntax.· ⟧ctx = Unit
⟦ Δ Syntax., X ⟧ctx = Σ[ δ ∈ ⟦ Δ ⟧ctx ] ⟦ X ⟧ty δ

⟦ Syntax.· ⟧subst = λ _ → tt
⟦ δ Syntax., x ⟧subst = ⟦ δ ⟧subst
⟦ Syntax.id ⟧subst = λ z → z
⟦ δ Syntax.∘ δ₁ ⟧subst = λ z → ⟦ δ ⟧subst (⟦ δ₁ ⟧subst z)
⟦ Syntax.π₁ ⟧subst = fst
⟦ Syntax.∘∘ δ δ' δ'' i ⟧subst = λ z → ⟦ δ'' ⟧subst (⟦ δ' ⟧subst (⟦ δ ⟧subst z))
⟦ Syntax.id∘ δ i ⟧subst = λ z → ⟦ δ ⟧subst z
⟦ Syntax.∘id δ i ⟧subst = λ z → ⟦ δ ⟧subst z
⟦ Syntax.·-uniq δ δ' i ⟧subst = λ _ → tt

⟦ Syntax.bit ⟧ty δ = Bool
⟦ X Syntax.[ γ ] ⟧ty δ = ⟦ X ⟧ty (⟦ γ ⟧subst δ)
⟦ Syntax.subst-∘ A δ' δ'' i ⟧ty δ = ⟦ A ⟧ty (⟦ δ' ⟧subst (⟦ δ'' ⟧subst δ))
⟦ Syntax.subst-id A i ⟧ty δ = ⟦ A ⟧ty δ

⟦ Syntax.var ⟧tm = λ δ → δ .snd
⟦ M Syntax.[ γ ] ⟧tm = λ δ → ⟦ M ⟧tm (⟦ γ ⟧subst δ)
⟦ Syntax.tru ⟧tm = λ δ → true
⟦ Syntax.fls ⟧tm = λ δ → false

⟦ Syntax.ε ⟧gctx δ = ε
⟦ Γ₁ Syntax.⊗ Γ₂ ⟧gctx δ = ⟦ Γ₁ ⟧gctx δ ⊗ ⟦ Γ₂ ⟧gctx δ
⟦ Syntax.ε⊗ {Γ} i ⟧gctx δ =
  StrongEquivalence→Path (⊗-unit-l-StrEq {g = ⟦ Γ ⟧gctx δ}) i
⟦ Syntax.⊗ε {Γ} i ⟧gctx δ =
  StrongEquivalence→Path (⊗-unit-r-StrEq {g = ⟦ Γ ⟧gctx δ}) i
⟦ Syntax.⊗⊗ {Γ₁}{Γ₂}{Γ₃} i ⟧gctx δ =
  StrongEquivalence→Path
    (⊗-assoc-StrEq {g = ⟦ Γ₁ ⟧gctx δ}{h = ⟦ Γ₂ ⟧gctx δ}{k = ⟦ Γ₃ ⟧gctx δ}) i
⟦ Syntax.ty A ⟧gctx = ⟦ A ⟧gty
⟦ Γ Syntax.[ δ' ] ⟧gctx δ = ⟦ Γ ⟧gctx (⟦ δ' ⟧subst δ)

⟦ Syntax.lit c ⟧gty δ = literal c 
⟦ Syntax.ε ⟧gty δ = ε
⟦ A Syntax.⊗ B ⟧gty δ = ⟦ A ⟧gty δ ⊗ ⟦ B ⟧gty δ
⟦ Syntax.⊥ ⟧gty δ = ⊥-grammar
⟦ A Syntax.⊕ B ⟧gty δ = ⟦ A ⟧gty δ ⊕ ⟦ B ⟧gty δ
⟦ Syntax.Star A ⟧gty δ = KL* (⟦ A ⟧gty δ)
⟦ A Syntax.[ δ' ] ⟧gty δ = ⟦ A ⟧gty (⟦ δ' ⟧subst δ)
⟦ A Syntax.⊸ B ⟧gty δ = ⟦ A ⟧gty δ ⊸ ⟦ B ⟧gty δ
⟦ A Syntax.⟜ B ⟧gty δ = ⟦ A ⟧gty δ ⟜ ⟦ B ⟧gty δ
⟦ Syntax.subst-id A i ⟧gty δ = λ z → ⟦ A ⟧gty δ z

⟦ Syntax.var ⟧gtm δ = id
-- ⟦ M Syntax.,⊗ N ⟧gtm δ = ⟦ M ⟧gtm δ ,⊗ ⟦ N ⟧gtm δ
⟦ M Syntax.[ γ ]l ⟧gtm δ = ⟦ M ⟧gtm δ ∘g ⟦ γ ⟧gsubst δ
-- ⟦ Syntax.⊗-L M ⟧gtm δ = ⟦ M ⟧gtm δ ∘g id ,⊗ ⊗-assoc
⟦ M Syntax.[ δ₁ ] ⟧gtm δ = ⟦ M ⟧gtm (⟦ δ₁ ⟧subst δ)
⟦ Syntax.ε-L M ⟧gtm δ = ⟦ M ⟧gtm δ ∘g id ,⊗ ⊗-unit-l⁻
⟦ Syntax.⟨⟩ ⟧gtm δ = λ w z → z
-- ⟦ Syntax.⊸-app ⟧gtm δ = ⊸-app
-- ⟦ Syntax.⊸-intro M ⟧gtm δ = ⊸-intro (⟦ M ⟧gtm δ)
-- ⟦ Syntax.⟜-app ⟧gtm δ = ⟜-app
-- ⟦ Syntax.⟜-intro M ⟧gtm δ = ⟜-intro (⟦ M ⟧gtm δ)
-- ⟦ Syntax.⊥-L ⟧gtm δ = ⊸-intro⁻ (⟜-intro⁻ ⊥-elim)
-- ⟦ Syntax.inl ⟧gtm δ = ⊕-inl
-- ⟦ Syntax.inr ⟧gtm δ = ⊕-inr
-- ⟦ Syntax.⊕-L M N ⟧gtm δ = ⊸-intro⁻ (⟜-intro⁻ (⊕-elim
--   (⟜-intro (⊸-intro (⟦ M ⟧gtm δ)))
--   (⟜-intro (⊸-intro (⟦ N ⟧gtm δ)))))
-- ⟦ Syntax.nil ⟧gtm δ = nil
-- ⟦ Syntax.cons ⟧gtm δ = cons
-- ⟦ Syntax.fold Mn Mc ⟧gtm δ =
--   foldKL*r _ (record { the-ℓ = _ ; G = _
--     ; nil-case = ⟦ Mn ⟧gtm δ
--     ; cons-case = ⟦ Mc ⟧gtm δ })

⟦ Syntax.id ⟧gsubst δ = id
⟦ γ' Syntax.∘ γ ⟧gsubst δ = ⟦ γ' ⟧gsubst δ ∘g ⟦ γ ⟧gsubst δ
⟦ γ₁ Syntax.,⊗ γ₂ ⟧gsubst δ = ⟦ γ₁ ⟧gsubst δ ,⊗ ⟦ γ₂ ⟧gsubst δ
