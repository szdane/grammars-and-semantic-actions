{-# OPTIONS --allow-unsolved-metas #-}
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module Metatheory.Simple.Syntax (Σ₀ : hSet ℓ-zero) where

open import Cubical.Foundations.Structure
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Data.Empty hiding (⊥)
open import Cubical.Data.Sigma
open import Cubical.Data.Sum
open import Cubical.Data.List as List hiding ([_])
open import Cubical.Data.FinData
open import Cubical.Data.Unit

infixr 5 _⊗_
infixr 5 _⊗c_
infixr 9 _∘s_
data Ty : Type ℓ-zero where
  lit : ⟨ Σ₀ ⟩ → Ty
  ⊥ ε : Ty
  _⊗_ _⊕_ : Ty → Ty → Ty
  --  _⊸_ _⟜_ : Ty → Ty → Ty
  Star : Ty → Ty

data Ctx : Type ℓ-zero where
  ty : Ty → Ctx
  εc : Ctx
  _⊗c_ : Ctx → Ctx → Ctx
  εc⊗c : ∀ {Γ} → εc ⊗c Γ ≡ Γ
  ⊗cεc : ∀ {Γ} → Γ ⊗c εc ≡ Γ
  ⊗c⊗c : ∀ {Γ₁ Γ₂ Γ₃} → (Γ₁ ⊗c Γ₂) ⊗c Γ₃ ≡ Γ₁ ⊗c Γ₂ ⊗c Γ₃

data Subst : Ctx → Ctx → Type ℓ-zero
data Tm : Ctx → Ty → Type ℓ-zero
data Subst where
  ids : ∀ {Γ} → Subst Γ Γ
  _∘s_ : ∀ {Γ Γ' Γ''} → Subst Γ' Γ'' → Subst Γ Γ' → Subst Γ Γ''
  _,⊗s_ : ∀ {Γ₁ Γ₂ Γ₁' Γ₂'}
    → Subst Γ₁ Γ₁' → Subst Γ₂ Γ₂'
    → Subst (Γ₁ ⊗c Γ₂) (Γ₁' ⊗c Γ₂')
  tys : ∀ {Γ A} → Tm Γ A → Subst Γ (ty A)
  ids∘s : ∀ {Γ Γ'} (γ : Subst Γ Γ') → ids ∘s γ ≡ γ
  ∘s∘s : ∀ {Γ Γ' Γ'' Γ'''} (γ : Subst Γ Γ')(γ' : Subst Γ' Γ'')(γ'' : Subst Γ'' Γ''')
    → (γ'' ∘s γ') ∘s γ ≡ γ'' ∘s γ' ∘s γ

data Tm where
    var : ∀ {A} → Tm (ty A) A
    _[_] : ∀ {Γ Γ' A} → Tm Γ A → Subst Γ' Γ → Tm Γ' A
    ⟨⟩ : Tm εc ε
    ε-L : ∀ {Γ₁ Γ₂ Γ}
      → Tm (Γ₁ ⊗c ty ε ⊗c Γ₂) Γ
      → Tm (Γ₁ ⊗c Γ₂) Γ
    _,⊗_ : ∀ {Γ₁ Γ₂ A₁ A₂} → Tm Γ₁ A₁ → Tm Γ₂ A₂ → Tm (Γ₁ ⊗c Γ₂) (A₁ ⊗ A₂)
    ⊗-L : ∀ {Γ₁ A₁ A₂ Γ₂ Γ'}
      → Tm (Γ₁ ⊗c ty (A₁ ⊗ A₂) ⊗c Γ₂) Γ'
      → Tm (Γ₁ ⊗c ty A₁ ⊗c ty A₂ ⊗c Γ₂) Γ'
    -- ⊸-app : ∀ {A B} → Tm (ty A ⊗ ty (A ⊸ B)) B
    -- ⊸-intro : ∀ {Γ A B}
    --   → Tm (ty A ⊗ Γ) B
    --   → Tm Γ (A ⊸ B)
    -- ⟜-app : ∀ {A B} → Tm (ty (B ⟜ A) ⊗ ty A) B
    -- ⟜-intro : ∀ {Γ A B}
    --   → Tm (Γ ⊗ ty A) B
    --   → Tm Γ (B ⟜ A)
    -- -- ⊥-L : ∀ {Γ₁ Γ₂ A} → Tm (Γ₁ ⊗ ty ⊥ ⊗ Γ₂) A
    inl : ∀ {A B} → Tm (ty A) (A ⊕ B)
    inr : ∀ {A B} → Tm (ty B) (A ⊕ B)
    -- ⊕-L : ∀ {Γ₁ Γ₂ A B C}
    --   → Tm (Γ₁ ⊗ ty A ⊗ Γ₂) C
    --   → Tm (Γ₁ ⊗ ty B ⊗ Γ₂) C
    --   → Tm (Γ₁ ⊗ ty (A ⊕ B) ⊗ Γ₂) C

    nil : ∀ {A} → Tm εc (Star A)
    cons : ∀ {A} → Tm (ty A ⊗c ty (Star A)) (Star A)
    -- -- todo: more general version? e.g., parameterized?
    -- fold : ∀ {A C} → Tm ε C → Tm (ty A ⊗ ty C) C
    --   → Tm (ty (Star A)) C

    subst-id : ∀ {Γ A} (M : Tm Γ A) → M [ ids ] ≡ M
    subst-∘ : ∀ {Γ Γ' Γ'' A} (M : Tm Γ A)(γ : Subst Γ' Γ)(γ' : Subst Γ'' Γ')
      → (M [ γ ∘s γ' ]) ≡ (M [ γ ] [ γ' ])
    var-tys : ∀ {Γ A} (M : Tm Γ A) → var [ tys M ] ≡ M


-- Some monoidal lemmas we need later that should follow from general principles
λ≡ρ : Path (εc ⊗c εc ≡ εc) ⊗cεc εc⊗c
λ≡ρ = {!!}

mon-lem' : ∀ Γ Γ' →
  Path (((Γ ⊗c Γ') ⊗c εc) ≡ (Γ ⊗c Γ')) ⊗cεc (⊗c⊗c ∙ (λ i → Γ ⊗c ⊗cεc {Γ = Γ'} i))
mon-lem' = {!!}


