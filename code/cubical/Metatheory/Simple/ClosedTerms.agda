open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module Metatheory.Simple.ClosedTerms (Σ₀ : hSet _) where

open import Cubical.Foundations.Structure
open import Cubical.Data.Empty hiding (⊥)
open import Cubical.Data.Sigma
open import Cubical.Data.Sum
open import Cubical.Data.List as List
open import Cubical.Data.Unit

import Metatheory.Simple.Syntax Σ₀ as Syntax
open import Grammar Σ₀
open import Grammar.Equivalence Σ₀
open import Grammar.MonoidalClosed Σ₀
open import Term Σ₀

-- First we define the "syntactic semantics" where we interpret types
-- as grammars syntactically by considering all terms in context w to
-- be parses of a string w. Then terms can act as parse transformers
-- using substitution.

private
  variable
    Γ Γ' Γ'' : Syntax.Ctx
    A A' A'' : Syntax.Ty
    M M' M'' : Syntax.Tm Γ A
    γ γ' γ'' : Syntax.Subst Γ Γ'
opaque
  ClosedTm : (A : Syntax.Ty) → Grammar ℓ-zero
  ClosedTm A w = Syntax.Tm (Syntax.⌈ w ⌉) A

  ClosedSubst : (Γ : Syntax.Ctx) → Grammar ℓ-zero
  ClosedSubst Γ w = Syntax.Subst (Syntax.⌈ w ⌉) Γ

  close-tm : ∀ {Γ A} → Syntax.Tm Γ A → ClosedSubst Γ ⊢ ClosedTm A
  close-tm M w γ = M Syntax.[ γ ]

  close-tm' : ∀ {A A'} → Syntax.Tm (Syntax.ty A) A' → ClosedTm A ⊢ ClosedTm A'
  close-tm' M w M' = M Syntax.[ Syntax.tys M' ]

  close-subst : ∀ {Γ Γ'} → Syntax.Subst Γ Γ' → ClosedSubst Γ ⊢ ClosedSubst Γ'
  close-subst γ w γ' = γ Syntax.∘s γ'

  close-tys : ClosedTm A ⊢ ClosedSubst (Syntax.ty A)
  close-tys M = Syntax.tys

-- There's various properties of this that we need: preserves substitution, 
  -- close-tm-subst : close-tm M ∘g close-subst γ ≡ close-tm (M Syntax.[ γ ])
  -- close-subst-id : close-subst {Γ = Γ} Syntax.ids ≡ id
  -- close-subst-∘ : close-subst (γ Syntax.∘s γ') ≡ close-subst γ ∘g close-subst γ'
-- laxly preserves monoidal structure...

  lax-ty⊗ : ∀ {A₁ A₂} → (ClosedTm A₁ ⊗ ClosedTm A₂) ⊢ ClosedTm (A₁ Syntax.⊗ A₂)
  lax-ty⊗ = ⊗-elim (λ w1 w2 M₁ M₂ → (M₁ Syntax.,⊗ M₂) Syntax.[ Syntax.⌈++⌉-subst w1 w2 ])

  lax-ctx⊗ : ∀ {Γ₁ Γ₂} → (ClosedSubst Γ₁ ⊗ ClosedSubst Γ₂) ⊢ ClosedSubst (Γ₁ Syntax.⊗c Γ₂)
  lax-ctx⊗ = ⊗-elim (λ w1 w2 γ1 γ2 → (γ1 Syntax.,⊗s γ2) Syntax.∘s Syntax.⌈++⌉-subst w1 w2)

  lax-tyε : ε ⊢ ClosedTm Syntax.ε
  lax-tyε = ε-elim Syntax.⟨⟩

  lax-ctxε : ε ⊢ ClosedSubst Syntax.εc
  lax-ctxε = ε-elim Syntax.ids

  -- lax-ty-naturality :
  --   ∀ {Γ₁ Γ₂ A₁ A₂}
  --   (M₁ : Syntax.Tm Γ₁ A₁)
  --   (M₂ : Syntax.Tm Γ₂ A₂)
  --   → lax-ty A₁ A₂ ∘g (close-tm M₁ ,⊗ close-tm M₂)
  --     ≡ close-tm (M₁ Syntax.,⊗ M₂) ∘g lax-ctx Γ₁ Γ₂
  -- lax-ty-naturality = {!!}

  litTm : ∀ {c} → Syntax.Tm (Syntax.ty (Syntax.lit c)) A → ClosedTm A [ c ]
  litTm {A = A} M = subst (λ Γ → Syntax.Tm Γ A) (sym Syntax.⊗cεc) M

  εTm : Syntax.Tm Syntax.εc A → ClosedTm A []
  εTm = λ z → z

  εSubst : Syntax.Subst Syntax.εc Γ → ClosedSubst Γ []
  εSubst = λ z → z
