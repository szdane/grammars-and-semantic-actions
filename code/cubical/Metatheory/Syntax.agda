open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module Metatheory.Syntax {ℓa} (Σ₀ : hSet ℓa) where

open import Cubical.Foundations.Structure
open import Cubical.Data.Empty hiding (⊥)
open import Cubical.Data.Sigma
open import Cubical.Data.Sum
open import Cubical.Data.FinData
open import Cubical.Data.Unit

private
  variable
    ℓ ℓ' ℓ'' ℓ''' ℓ'''' ℓx ℓy ℓb ℓg ℓg' ℓh ℓh' : Level

module _ where
  data Ctx : Type ℓa
  data Subst : (Δ : Ctx) → Ctx → Type ℓa
  data Ty (Γ : Ctx) : Type ℓa
  data Tm  : (Δ : Ctx) → (Ty Δ) → Type ℓa

  data Ctx where
    · : Ctx
    _,_ : (Δ : Ctx) → Ty Δ → Ctx

  _∘subst_ : ∀ {Θ Δ Γ} → Subst Θ Γ → Subst Δ Θ → Subst Δ Γ
  data Ty Γ where
    bit : Ty Γ
    _[_] : ∀ {Δ} → Ty Δ → Subst Γ Δ → Ty Γ
    subst-∘ : ∀ {Δ Δ' A}{δ' : Subst Δ Δ'}{δ : Subst Γ Δ}
      → ((A [ δ' ]) [ δ ]) ≡
      (A [ δ' ∘subst δ ])
    subst-bit : ∀ {Δ}{δ : Subst Γ Δ} → bit [ δ ] ≡ bit
  data Subst where
    · : ∀ {Δ} → Subst Δ ·
    _,_ : ∀ {Γ Δ A} → (γ : Subst Δ Γ) → (Tm Δ (A [ γ ])) → Subst Δ Γ
    id  : ∀ {Δ} → Subst Δ Δ
    _∘_ : ∀ {Θ Δ Γ} → Subst Θ Γ → Subst Δ Θ → Subst Δ Γ
    π₁ : ∀ {Δ A} → Subst (Δ , A) Δ
  _∘subst_ = _∘_

  data Tm where
    var : ∀ {Δ A} → Tm (Δ , A) (A [ π₁ ])
    _[_] : ∀ {Δ Γ A} → Tm Γ A → (γ : Subst Δ Γ) → Tm Δ (A [ γ ])
    tru : ∀ {Δ} → Tm Δ bit
    fls : ∀ {Δ} → Tm Δ bit

  data GTy (Δ : Ctx) : Type ℓa where
    lit : ⟨ Σ₀ ⟩ → GTy Δ
    ε : GTy Δ
    _⊗_ : GTy Δ → GTy Δ → GTy Δ
    _⊸_ : GTy Δ → GTy Δ → GTy Δ
    _⟜_ : GTy Δ → GTy Δ → GTy Δ
    ⊥ : GTy Δ
    _⊕_ : GTy Δ → GTy Δ → GTy Δ
    Star : GTy Δ → GTy Δ
    _[_] : ∀ {Δ'} → GTy Δ' → Subst Δ Δ' → GTy Δ

  -- todo: full on bunches
  data GCtx (Δ : Ctx) : Type ℓa where
    ε : GCtx Δ
    _⊗_ : GCtx Δ → GCtx Δ → GCtx Δ
    ε⊗ : ∀ {A} → ε ⊗ A ≡ A
    ⊗ε : ∀ {A} → A ⊗ ε ≡ A
    ⊗⊗ : ∀ {A B C} → (A ⊗ B) ⊗ C ≡ A ⊗ (B ⊗ C)
    ty : GTy Δ → GCtx Δ
    _[_] : ∀ {Δ'} → GCtx Δ' → Subst Δ Δ' → GCtx Δ
    -- presheaf laws for _[_]?
    -- pentagon/triangle laws?
  infixr 5 _⊗_

  data GSubst {Δ : Ctx} : GCtx Δ → GCtx Δ → Type ℓa where
    id : ∀ {Γ} → GSubst Γ Γ
    _∘_ : ∀ {Γ Γ' Γ''} → GSubst Γ' Γ'' → GSubst Γ Γ' → GSubst Γ Γ''
    _,⊗_ : ∀ {Γ₁ Γ₂ Γ₁' Γ₂'}
      → GSubst Γ₁ Γ₁' → GSubst Γ₂ Γ₂'
      → GSubst (Γ₁ ⊗ Γ₂) (Γ₁' ⊗ Γ₂')
    -- todo: equations?

  data GTm {Δ : Ctx} : GCtx Δ → GTy Δ → Type ℓa where
    _[_] : ∀ {Δ'}{Γ : GCtx Δ'}{A} → GTm Γ A → ∀ δ → GTm (Γ [ δ ]) (A [ δ ])
    var : ∀ {A} → GTm (ty A) A
    _[_]l : ∀ {Γ Γ' A} → GTm Γ A → GSubst Γ' Γ → GTm Γ' A
    ε-L : ∀ {Γ₁ Γ₂ Γ}
      → GTm (Γ₁ ⊗ ty ε ⊗ Γ₂) Γ
      → GTm (Γ₁ ⊗ Γ₂) Γ
    _,⊗_ : ∀ {Γ₁ Γ₂ A₁ A₂} → GTm Γ₁ A₁ → GTm Γ₂ A₂ → GTm (Γ₁ ⊗ Γ₂) (A₁ ⊗ A₂)
    ⊗-L : ∀ {Γ₁ A₁ A₂ Γ₂ Γ'}
      → GTm (Γ₁ ⊗ ty (A₁ ⊗ A₂) ⊗ Γ₂) Γ'
      → GTm (Γ₁ ⊗ ty A₁ ⊗ ty A₂ ⊗ Γ₂) Γ'
    ⊸-app : ∀ {A B} → GTm (ty A ⊗ ty (A ⊸ B)) B
    ⊸-intro : ∀ {Γ A B}
      → GTm (ty A ⊗ Γ) B
      → GTm Γ (A ⊸ B)
    ⟜-app : ∀ {A B} → GTm (ty (B ⟜ A) ⊗ ty A) B
    ⟜-intro : ∀ {Γ A B}
      → GTm (Γ ⊗ ty A) B
      → GTm Γ (B ⟜ A)
    ⊥-L : ∀ {Γ₁ Γ₂ A} → GTm (Γ₁ ⊗ ty ⊥ ⊗ Γ₂) A
    inl : ∀ {A B} → GTm (ty A) (A ⊕ B)
    inr : ∀ {A B} → GTm (ty B) (A ⊕ B)
    ⊕-L : ∀ {Γ₁ Γ₂ A B C}
      → GTm (Γ₁ ⊗ ty A ⊗ Γ₂) C
      → GTm (Γ₁ ⊗ ty B ⊗ Γ₂) C
      → GTm (Γ₁ ⊗ ty (A ⊕ B) ⊗ Γ₂) C

    nil : ∀ {A} → GTm ε (Star A)
    cons : ∀ {A} → GTm (ty A ⊗ ty (Star A)) (Star A)
    -- todo: more general version? e.g., parameterized?
    fold : ∀ {A C} → GTm ε C → GTm (ty A ⊗ ty C) C
      → GTm (ty (Star A)) C

    -- TODO: equations?
