open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module Metatheory.CanonicitySemantics (Σ₀ : hSet _) where

open import Cubical.Foundations.Structure
open import Cubical.Data.Empty hiding (⊥)
open import Cubical.Data.Sigma
open import Cubical.Data.Sum
open import Cubical.Data.FinData
open import Cubical.Data.Unit

import Metatheory.Syntax Σ₀ as Syntax
open import Grammar Σ₀
open import Grammar.KleeneStar Σ₀
open import Grammar.Equivalence Σ₀
open import Term Σ₀

-- the dependent types are interpreted as families over *closed* terms
⟦_⟧ctx : (Δ : Syntax.Ctx) → Syntax.Subst Syntax.· Δ → Type ℓ-zero
⟦_⟧subst : ∀ {Δ Δ'} → (δ' : Syntax.Subst Δ Δ') → ∀ δ → ⟦ Δ ⟧ctx δ → ⟦ Δ' ⟧ctx (δ' Syntax.∘ δ)
⟦_⟧ty : ∀ {Δ} → (A : Syntax.Ty Δ) → ∀ δ → ⟦ Δ ⟧ctx δ → Syntax.Tm Syntax.· (A Syntax.[ δ ]) → Type ℓ-zero
⟦_⟧tm : ∀ {Δ A} → (M : Syntax.Tm Δ A) → ∀ δ → (δ~ : ⟦ Δ ⟧ctx δ) → ⟦ A ⟧ty δ δ~ (M Syntax.[ δ ])

⟦ Syntax.· ⟧ctx δ = Unit
⟦ Δ Syntax., A ⟧ctx δ =
  Σ[ δ1~ ∈ ⟦ Δ ⟧ctx δ1 ]
  ⟦ A ⟧ty δ1 δ1~ (subst (Syntax.Tm Syntax.·) Syntax.subst-∘ (Syntax.var Syntax.[ δ ]))
  where
    δ1 = Syntax.π₁ Syntax.∘ δ

⟦ Syntax.bit ⟧ty δ δ~ M = (M' ≡ Syntax.tru) ⊎ (M' ≡ Syntax.fls)
  where M' : Syntax.Tm Syntax.· Syntax.bit
        M' = subst (Syntax.Tm Syntax.·) Syntax.subst-bit M
⟦ A Syntax.[ δ' ] ⟧ty δ δ~ M = {!!}
⟦ Syntax.subst-∘ i ⟧ty δ = {!!}
⟦ Syntax.subst-bit i ⟧ty δ = {!!}

-- ⟦_⟧gctx : ∀ {Δ} → Syntax.GCtx Δ → ⟦ Δ ⟧ctx → Grammar ℓ-zero
-- ⟦_⟧gty  : ∀ {Δ} → Syntax.GTy Δ → ⟦ Δ ⟧ctx → Grammar ℓ-zero
-- ⟦_⟧gsubst : ∀ {Δ Γ Γ'} → Syntax.GSubst Γ Γ' → (δ : ⟦ Δ ⟧ctx) → ⟦ Γ ⟧gctx δ ⊢ ⟦ Γ' ⟧gctx δ
-- ⟦_⟧gtm : ∀ {Δ Γ A} → Syntax.GTm Γ A → (δ : ⟦ Δ ⟧ctx) → ⟦ Γ ⟧gctx δ ⊢ ⟦ A ⟧gty δ
